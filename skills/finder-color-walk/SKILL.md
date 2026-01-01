# Finder Color Walk Skill

**Status**: ✅ Production Ready  
**Trit**: 0 (ERGODIC - coordination)  
**Principle**: Random walk over files → deterministic Finder colors  
**Integration**: Gay.jl colors → macOS Finder labels

---

## Overview

**Finder Color Walk** traverses directories using deterministic random walks and assigns macOS Finder label colors based on Gay.jl's SplitMix64 color generation. Each file gets a reproducible color from the same seed.

```
seed → SplitMix64 → hue → Finder label
```

## macOS Finder Label Colors

| Index | Color  | Hue Range | Trit | GF(3) Role |
|-------|--------|-----------|------|------------|
| 0     | None   | -         | -    | Clear      |
| 1     | Gray   | neutral   | 0    | ERGODIC    |
| 2     | Green  | 120°      | 0    | ERGODIC    |
| 3     | Purple | 270°      | -1   | MINUS      |
| 4     | Blue   | 240°      | -1   | MINUS      |
| 5     | Yellow | 60°       | 0    | ERGODIC    |
| 6     | Orange | 30°       | +1   | PLUS       |
| 7     | Red    | 0°        | +1   | PLUS       |

## Hue to Finder Label Mapping

```python
def hue_to_finder_label(hue: float) -> int:
    """Map Gay.jl hue (0-360°) to Finder label (1-7)."""
    if 0 <= hue < 30:
        return 7   # Red
    elif 30 <= hue < 60:
        return 6   # Orange
    elif 60 <= hue < 90:
        return 5   # Yellow
    elif 90 <= hue < 150:
        return 2   # Green
    elif 150 <= hue < 210:
        return 4   # Blue
    elif 210 <= hue < 270:
        return 4   # Blue
    elif 270 <= hue < 330:
        return 3   # Purple
    else:
        return 7   # Red (330-360)

def trit_to_finder_label(trit: int) -> int:
    """Map GF(3) trit to Finder label."""
    return {
        -1: 4,  # MINUS → Blue
         0: 2,  # ERGODIC → Green
        +1: 7,  # PLUS → Red
    }[trit]
```

## Core Algorithm

```python
from gay import SplitMixTernary
import subprocess
import os

class FinderColorWalk:
    """Random walk over files with Finder color assignment."""
    
    def __init__(self, seed: int, directory: str):
        self.gen = SplitMixTernary(seed)
        self.directory = directory
        self.walk_log = []
    
    def set_finder_label(self, filepath: str, label: int):
        """Set macOS Finder label color (0-7)."""
        script = f'''
        tell application "Finder"
            set theFile to POSIX file "{filepath}" as alias
            set label index of theFile to {label}
        end tell
        '''
        subprocess.run(['osascript', '-e', script], check=True)
    
    def color_file(self, filepath: str, index: int) -> dict:
        """Assign color to file based on walk index."""
        color = self.gen.color_at(index)
        label = hue_to_finder_label(color['H'])
        
        self.set_finder_label(filepath, label)
        
        result = {
            'file': filepath,
            'index': index,
            'color': color,
            'finder_label': label,
            'trit': color['trit']
        }
        self.walk_log.append(result)
        return result
    
    def walk_directory(self, max_files: int = 100) -> list:
        """Random walk through directory, coloring files."""
        files = []
        for root, dirs, filenames in os.walk(self.directory):
            for f in filenames:
                files.append(os.path.join(root, f))
        
        # Shuffle deterministically based on seed
        indices = list(range(len(files)))
        for i in range(len(indices) - 1, 0, -1):
            j = self.gen.next_u64() % (i + 1)
            indices[i], indices[j] = indices[j], indices[i]
        
        # Color files in walk order
        results = []
        for walk_step, file_idx in enumerate(indices[:max_files]):
            result = self.color_file(files[file_idx], walk_step)
            results.append(result)
        
        return results
    
    def verify_gf3(self) -> bool:
        """Verify GF(3) conservation across walk."""
        total = sum(entry['trit'] for entry in self.walk_log)
        return total % 3 == 0
```

## Shell Commands

```bash
# Color files in a directory with seed
finder-color-walk ~/Documents 0x42D

# Color with trit-based labels (simpler)
finder-color-walk --trit ~/Projects 1069

# Clear all Finder labels in directory
finder-color-clear ~/Documents

# Show walk log
finder-color-log 0x42D
```

## Babashka Implementation

```clojure
#!/usr/bin/env bb
;; finder_color_walk.bb

(require '[babashka.process :refer [shell]])

(def GOLDEN 0x9E3779B97F4A7C15)
(def MIX1 0xBF58476D1CE4E5B9)
(def MIX2 0x94D049BB133111EB)
(def MASK64 0xFFFFFFFFFFFFFFFF)

(defn splitmix64 [state]
  (let [z (bit-and (+ state GOLDEN) MASK64)
        z (bit-and (* (bit-xor z (unsigned-bit-shift-right z 30)) MIX1) MASK64)
        z (bit-and (* (bit-xor z (unsigned-bit-shift-right z 27)) MIX2) MASK64)]
    [(bit-xor z (unsigned-bit-shift-right z 31)) z]))

(defn color-at [seed index]
  (loop [state seed i 0]
    (let [[rand new-state] (splitmix64 state)]
      (if (= i index)
        (let [h (* 360.0 (/ (double rand) (double MASK64)))
              trit (cond
                     (or (< h 60) (>= h 300)) 1
                     (< h 180) 0
                     :else -1)]
          {:hue h :trit trit})
        (recur new-state (inc i))))))

(defn hue->finder-label [hue]
  (cond
    (< hue 30) 7    ; Red
    (< hue 60) 6    ; Orange
    (< hue 90) 5    ; Yellow
    (< hue 150) 2   ; Green
    (< hue 270) 4   ; Blue
    (< hue 330) 3   ; Purple
    :else 7))       ; Red

(defn set-finder-label! [filepath label]
  (let [script (format "tell application \"Finder\"
                          set theFile to POSIX file \"%s\" as alias
                          set label index of theFile to %d
                        end tell" filepath label)]
    (shell "osascript" "-e" script)))

(defn walk-and-color! [directory seed max-files]
  (let [files (->> (file-seq (io/file directory))
                   (filter #(.isFile %))
                   (take max-files)
                   (map str))]
    (doseq [[idx filepath] (map-indexed vector files)]
      (let [{:keys [hue trit]} (color-at seed idx)
            label (hue->finder-label hue)]
        (println (format "  %d: %s → label=%d (trit=%+d)" 
                         idx (last (str/split filepath #"/")) label trit))
        (set-finder-label! filepath label)))))

;; CLI
(when (= *file* (System/getProperty "babashka.file"))
  (let [[dir seed-str max-str] *command-line-args*
        seed (Long/parseLong (or seed-str "1069") 16)
        max-files (Integer/parseInt (or max-str "20"))]
    (println (format "🎨 FINDER COLOR WALK: %s (seed=0x%X)" dir seed))
    (walk-and-color! dir seed max-files)
    (println "✓ Done")))
```

## Justfile Recipes

```just
# Color files in directory
finder-color-walk dir seed="0x42D" max="20":
    @echo "🎨 FINDER COLOR WALK: {{dir}}"
    bb ~/.agents/skills/finder-color-walk/finder_color_walk.bb "{{dir}}" "{{seed}}" "{{max}}"

# Color with trit-based simple labels
finder-color-trit dir seed="1069":
    @echo "🎨 FINDER COLOR (trit mode): {{dir}}"
    python3 -c "
from pathlib import Path
import subprocess

GOLDEN = 0x9E3779B97F4A7C15
def splitmix(s):
    s = (s + GOLDEN) & 0xFFFFFFFFFFFFFFFF
    z = s
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & 0xFFFFFFFFFFFFFFFF
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & 0xFFFFFFFFFFFFFFFF
    return z ^ (z >> 31), s

def set_label(f, l):
    subprocess.run(['osascript', '-e', f'tell app \"Finder\" to set label index of (POSIX file \"{f}\" as alias) to {l}'])

seed = int('{{seed}}', 0)
files = list(Path('{{dir}}').rglob('*'))[:20]
for i, f in enumerate(files):
    if f.is_file():
        rand, seed = splitmix(seed)
        h = (rand / 0xFFFFFFFFFFFFFFFF) * 360
        trit = 1 if h < 60 or h >= 300 else (0 if h < 180 else -1)
        label = {-1: 4, 0: 2, 1: 7}[trit]
        print(f'  {i}: {f.name} → {[\"Blue\",\"Green\",\"Red\"][trit+1]}')
        set_label(str(f.absolute()), label)
"

# Clear all Finder labels
finder-color-clear dir:
    @echo "🧹 Clearing Finder labels in {{dir}}"
    find "{{dir}}" -type f -exec xattr -d com.apple.FinderInfo {} \; 2>/dev/null || true

# Demo: color current directory
finder-color-demo:
    @just finder-color-walk . 0x42D 10
```

## Integration with Random Walk Fusion

```python
from random_walk_fusion import RandomWalkFusion
from finder_color_walk import FinderColorWalk

def fused_skill_file_walk(seed: int, skill_dir: str, file_dir: str):
    """Walk skills AND files in parallel with same seed."""
    
    # Fork seed for parallel walks
    skill_walk = RandomWalkFusion(seed=seed, skills=load_skills(skill_dir))
    file_walk = FinderColorWalk(seed=seed, directory=file_dir)
    
    # Execute in parallel
    skill_path = skill_walk.forward(steps=10)
    file_results = file_walk.walk_directory(max_files=10)
    
    # Both use same seed → deterministic correlation
    return {
        'skill_path': skill_path,
        'file_colors': file_results,
        'gf3_skill': skill_walk.verify_gf3(),
        'gf3_files': file_walk.verify_gf3()
    }
```

## Example Output

```
🎨 FINDER COLOR WALK: ~/Projects (seed=0x42D)
  0: main.py → label=7 (trit=+1) [Red]
  1: utils.py → label=2 (trit=0) [Green]
  2: config.yaml → label=4 (trit=-1) [Blue]
  3: README.md → label=6 (trit=+1) [Orange]
  4: test_main.py → label=2 (trit=0) [Green]
  5: .gitignore → label=3 (trit=-1) [Purple]
  6: requirements.txt → label=5 (trit=0) [Yellow]
  
GF(3) Sum: 0 ≡ 0 (mod 3) ✓ Conserved
```

---

**Skill Name**: finder-color-walk  
**Type**: File System / Visual Organization  
**Trit**: 0 (ERGODIC)  
**GF(3)**: Conserved via trit assignment  
**Platform**: macOS only (uses Finder AppleScript)



## Scientific Skill Interleaving

This skill connects to the K-Dense-AI/claude-scientific-skills ecosystem:

### Stochastic
- **simpy** [○] via bicomodule

### Visualization
- **matplotlib** [○] via bicomodule
  - Hub for all visualization

### Bibliography References

- `graph-theory`: 38 citations in bib.duckdb

## Cat# Integration

This skill maps to **Cat# = Comod(P)** as a bicomodule in the equipment structure:

```
Trit: 0 (ERGODIC)
Home: Prof
Poly Op: ⊗
Kan Role: Adj
Color: #26D826
```

### GF(3) Naturality

The skill participates in triads satisfying:
```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```

This ensures compositional coherence in the Cat# equipment structure.
