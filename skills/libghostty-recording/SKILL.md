---
name: libghostty-recording
description: Record, stream, and replay libghostty-vt terminal sessions for documentation, debugging, and LLM training.
---
# libghostty-vt Recording Skill 📹

**Trit**: 0 (ERGODIC - Coordinator)
**GF(3) Triad**: `asciinema (-1) ⊗ libghostty-recording (0) ⊗ vhs (+1) = 0`

## Overview

Record, stream, and replay libghostty-vt terminal sessions for documentation, debugging, and LLM training.

## Recording Methods

### 1. Asciinema (Lightweight .cast)
```bash
# Record session
asciinema rec ~/recordings/session-$(date +%Y%m%d_%H%M%S).cast

# Auto-record all sessions (add to .zshrc)
asciinema rec --append ~/recordings/daily-$(date +%Y%m%d).cast

# Stream to server
asciinema rec -t "libghostty demo" https://asciinema.org
```

**Pros**: Compact, text-based, searchable, LLM-friendly  
**Cons**: No video export

### 2. Charmbracelet VHS (GIF/Video)
```tape
# demo.tape
Output demo.gif
Set FontSize 14
Set Width 1200
Set Height 600
Set Theme "Ghostty"

Type "echo 'libghostty-vt recording'"
Enter
Sleep 500ms
Type "skill load omniglot"
Enter
Sleep 1s
```

```bash
vhs demo.tape
```

**Pros**: Produces shareable GIFs, scriptable  
**Cons**: Larger files

### 3. libghostty-vt Native Hooks
```zig
// Hook into libghostty-vt stream
const recorder = ghostty_vt.Recorder.init(.{
    .output = "session.cast",
    .format = .asciinema_v2,
});

terminal.setOutputHook(recorder.hook);
```

## CI Gate Controls (on the way IN)

### Pre-Installation Validation
```yaml
# .github/workflows/skill-gate.yml
name: Skill Installation Gate

on:
  pull_request:
    paths:
      - 'skills/**'
      - 'SKILL.md'

jobs:
  validate-skills:
    runs-on: ubuntu-latest
    
    steps:
      - uses: actions/checkout@v4
      
      - name: Validate GF(3) conservation
        run: |
          # Sum all trits, must equal 0 mod 3
          python3 -c "
          import json
          skills = json.load(open('skills.json'))
          total = sum(s.get('trit', 0) for s in skills)
          assert total % 3 == 0, f'GF(3) violation: sum={total}'
          print('✓ GF(3) conserved')
          "
          
      - name: Check SKILL.md structure
        run: |
          for f in skills/*/SKILL.md; do
            grep -q "^# " "$f" || (echo "Missing title: $f" && exit 1)
            grep -q "Trit" "$f" || (echo "Missing trit: $f" && exit 1)
          done
          echo "✓ All skills have required structure"
          
      - name: Verify no placeholder tokens
        run: |
          ! grep -rE "(TODO|FIXME|placeholder|mock-|pseudo-)" skills/ || \
            (echo "❌ Placeholder tokens found" && exit 1)
```

### Local Gate
```bash
# Validate before install
validate-skills() {
  local repo=$1
  gh api repos/$repo/contents/skills.json -q '.content' | \
    base64 -d | python3 -c "
import json, sys
skills = json.load(sys.stdin)
total = sum(s.get('trit', 0) for s in skills)
if total % 3 != 0:
    print(f'❌ GF(3) violation: {total}')
    sys.exit(1)
print(f'✓ {len(skills)} skills, GF(3) conserved')
"
}

# Use before install
validate-skills plurigrid/asi && \
  npx ai-agent-skills install plurigrid/asi --agent codex
```

## LLM Training from Recordings

From asciinema discourse (2024):
> "My real interest is not so much in playing back the recordings but in using the `.cast` files for creating a vector database that I can then query and use an LLM to extract useful workflows."

### Cast File → Vector DB
```python
import json
import duckdb

def parse_cast(cast_file: str) -> list:
    """Extract commands and outputs from .cast file"""
    with open(cast_file) as f:
        lines = f.readlines()
    
    header = json.loads(lines[0])
    events = [json.loads(line) for line in lines[1:]]
    
    return [{
        "timestamp": e[0],
        "type": e[1],  # 'o' = output, 'i' = input
        "data": e[2]
    } for e in events]

# Store in DuckDB for querying
con = duckdb.connect("recordings.duckdb")
con.execute("""
    CREATE TABLE IF NOT EXISTS terminal_events (
        session_id VARCHAR,
        timestamp DOUBLE,
        event_type VARCHAR,
        data VARCHAR,
        embedding FLOAT[1024]
    )
""")
```

## Integration with libghostty-ewig

From [libghostty-ewig.jl](file:///Users/bob/ies/libghostty-ewig.jl):
```julia
# Connect libghostty-vt parsing to ewig modal editor
module LibghosttyEwig
    # VT escape sequence parsing
    # Gay.jl color integration
    # Modal editing state machine
end
```

## Best Practices

1. **Daily auto-recording**: Start asciinema on shell init
2. **Session naming**: `session-{date}_{project}_{task}.cast`
3. **Compression**: Cast files are JSON, gzip well
4. **Privacy**: Filter secrets with `asciinema rec --env=TERM`
5. **Playback speed**: `asciinema play -s 2 session.cast`

## Files

| Path | Purpose |
|------|---------|
| `~/recordings/` | Default recording directory |
| `~/.config/asciinema/` | Asciinema config |
| `~/ies/ghostty-vt-src/` | libghostty-vt source |

## References

- [asciinema/asciinema](https://github.com/asciinema/asciinema) - Terminal recorder
- [charmbracelet/vhs](https://github.com/charmbracelet/vhs) - CLI GIF recorder
- [libghostty-vt](https://mitchellh.com/writing/libghostty-is-coming) - Mitchell's blog post

## 490 Skills Installed ✓

```
npx ai-agent-skills install plurigrid/asi --agent codex
Installed 490 skill(s) from plurigrid/asi
```


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
