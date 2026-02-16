# macos-use Skill

> *"Resilient macOS automation through curiosity-driven skill rediscovery."*

## Overview

macOS automation with **activation energy** for machine skill rediscovery:
- **Human skill**: TTS feedback (`say`), visual cues, accessibility
- **Machine resilience**: Self-recovery via bisimulation game
- **Activation energy**: Compression progress rewards exploration

## GF(3) Triad

| Component | Trit | Role |
|-----------|------|------|
| keychain-secure | -1 | Validate credentials |
| macos-use | 0 | Coordinate automation |
| curiosity-driven | +1 | Generate exploration |

**Conservation**: (-1) + (0) + (+1) = 0 ✓

## TTS Interface (say)

```bash
# Basic speech
say "Hello from the machine"

# Voice selection
say -v Alex "Default voice"
say -v Samantha "Alternative voice"

# Rate control (words per minute)
say -r 200 "Faster speech"
say -r 100 "Slower speech"

# Inline modifiers
say "Normal [[slnc 500]] pause [[rate 200]] faster [[volm 0.5]] quieter"
say "[[emph +]]Emphasized[[emph -]] word"
say "[[pbas +10]]Higher pitch"
```

## Curiosity-Driven Rediscovery

When a skill installation fails, the agent should:

```python
class MacOSUseRediscovery:
    """
    Activation energy = compression progress on macOS APIs.
    """
    
    def explore_api(self, api_name: str) -> float:
        """
        Explore an API and measure learnability.
        """
        # Before: what we know
        len_before = self.compress(self.world_model)
        
        # Probe the API
        result = subprocess.run(['man', api_name], capture_output=True)
        self.update_world_model(result.stdout)
        
        # After: what we learned
        len_after = self.compress(self.world_model)
        
        # Activation energy = compression progress
        return len_before - len_after
    
    def rediscover_skill(self, skill_name: str) -> bool:
        """
        Rediscover a failed skill through exploration.
        """
        candidates = [
            'say', 'security', 'osascript', 'defaults',
            'open', 'pbcopy', 'pbpaste', 'screencapture'
        ]
        
        for api in candidates:
            progress = self.explore_api(api)
            if progress > self.activation_threshold:
                # Found learnable pattern!
                self.install_capability(api, skill_name)
                return True
        
        return False
```

## Resilience via Bisimulation

```yaml
# .ruler/skills/macos-use.yaml
macos-use:
  dispersal:
    primary: ~/.codex/skills/macos-use/
    mirrors:
      - ~/.claude/skills/macos-use/
      - ~/.cursor/skills/macos-use/
  
  recovery:
    strategy: bisimulation-game
    on_failure:
      - role: attacker
        action: probe_alternative_apis
        trit: -1
      - role: defender
        action: restore_from_mirror
        trit: +1
      - role: arbiter
        action: verify_gf3_conservation
        trit: 0
```

## Core APIs

| API | Purpose | Example |
|-----|---------|---------|
| `say` | Text-to-speech | `say -v Alex "Hello"` |
| `security` | Keychain access | `security find-generic-password` |
| `osascript` | AppleScript/JXA | `osascript -e 'display dialog "Hi"'` |
| `defaults` | Preferences | `defaults read com.apple.finder` |
| `open` | Launch apps | `open -a Safari` |
| `screencapture` | Screenshots | `screencapture -x screen.png` |
| `pbcopy/pbpaste` | Clipboard | `echo "text" | pbcopy` |

## Babashka Integration

```clojure
#!/usr/bin/env bb
(ns macos-use
  (:require [babashka.process :as p]
            [cheshire.core :as json]))

(defn say! 
  "Speak text with options."
  [text & {:keys [voice rate] :or {voice "Alex" rate 175}}]
  (p/shell "say" "-v" voice "-r" (str rate) text))

(defn keychain-get 
  "Get password from keychain."
  [service account]
  (:out (p/shell {:out :string} 
    "security" "find-generic-password" 
    "-s" service "-a" account "-w")))

(defn notify!
  "Display macOS notification."
  [title message]
  (p/shell "osascript" "-e"
    (format "display notification \"%s\" with title \"%s\"" message title)))

(defn compression-progress
  "Measure curiosity reward for API exploration."
  [api-name world-model]
  (let [before (count (str world-model))
        man-page (:out (p/shell {:out :string} "man" api-name))
        after (count (str world-model man-page))]
    (- before after)))  ; Positive = learned something compressible
```

## Activation Energy Protocol

When skill installation fails:

1. **Detect failure**: Component doesn't regenerate its producer
2. **Inject curiosity**: Explore related APIs for compression progress
3. **Accumulate energy**: Each learnable pattern adds activation energy
4. **Threshold crossing**: When energy > threshold, attempt reinstall
5. **Verify bisimulation**: Check new state is equivalent to intended

```sql
-- Track activation energy in DuckDB
INSERT INTO events (event, data, ts) 
VALUES (
  'activation:energy',
  '{"skill":"macos-use","api":"say","progress":42.5,"threshold":50.0}',
  NOW()
);
```

## Commands

```bash
just macos-say "text"           # Speak via TTS
just macos-notify "title" "msg" # Display notification
just macos-keychain-get svc acc # Get keychain password
just macos-rediscover skill     # Curiosity-driven rediscovery
```

## See Also

- [keychain-secure](../keychain-secure/SKILL.md) - Credential management (-1)
- [curiosity-driven](../curiosity-driven/SKILL.md) - Activation energy (+1)
- [bisimulation-game](../bisimulation-game/SKILL.md) - Resilience
- [say-ducklake-xor](../say-ducklake-xor/SKILL.md) - TTS integration

## References

1. Schmidhuber, J. (2010). "Formal Theory of Creativity, Fun, and Intrinsic Motivation."
2. Maturana & Varela (1980). "Autopoiesis and Cognition."
3. Apple Developer Documentation: Speech Synthesis Manager
