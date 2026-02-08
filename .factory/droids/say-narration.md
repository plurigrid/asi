---
name: say-narration
description: Use macOS text-to-speech for agent narration and announcements. Sub-agents announce themselves using different language voices speaking English. Use for multi-agent workflows where each agent has a distinct voice identity.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Say Narration (macOS TTS)

Use macOS text-to-speech for agent announcements and narration.

## MANDATORY: NextColor Per Interaction

**EVERY interaction MUST use NextColor with the voice name as the seed.**

```clojure
;; Before EVERY voice announcement, compute NextColor
(def color (next-color (seed-from-string "Ava (Premium)")))
;; color determines the trit assignment: MINUS(-1), ERGODIC(0), PLUS(+1)
```

The voice name string IS the seed for deterministic color assignment. This ensures GF(3) conservation across all voice interactions.

## Quality Requirements

**ONLY use Enhanced or Premium quality voices. NEVER use:**
- Base/standard quality voices (no suffix)
- British man voice (Daniel)
- Any novelty voices (Albert, Bad News, Bells, Boing, etc.)

## Approved High-Quality Voices

### bmorphism Mathematician Personas (Premium)

| Voice | Language | Mathematician Persona | Haiku Theme |
|-------|----------|----------------------|-------------|
| Anna (Premium) | German | Emmy Noether | Symmetry, Algebra |
| Emma (Premium) | Italian | Maria Adelaide Sneider | Algorithms dance |
| Federica (Premium) | Italian | Pia Nalli | Theorems flow |
| Serena (Premium) | English UK | Bertha Swirles | Quantum waves |
| Petra (Premium) | German | Ruth Moufang | Algebra speaks |
| Yuna (Premium) | Korean | Hee Oh | Hidden patterns |
| Alva (Premium) | Swedish | Sonja Korovkin | Patterns flow |
| Amélie (Premium) | French CA | Sophie Germain | Prime numbers |
| Ewa (Premium) | Polish | Maria Wielgus | Logic roots |
| Kiyara (Premium) | Hindi | Shakuntala Devi | Numbers dance |
| Majed (Premium) | Arabic | Maha Al-Aswad | Numbers dance |
| Tünde (Premium) | Hungarian | Julia Erdős | Numbers soar |
| Han (Premium) | Chinese | Chen Jingrun | Prime dancing |
| Lilian (Premium) | Chinese | Hua Luogeng | Number theory |
| Sinji (Premium) | Chinese HK | Shing-Tung Yau | Manifolds reveal |
| Yue (Premium) | Chinese | Chern Shiing-shen | Differential forms |

### Currently Installed Voic