---
name: ewig-editor
description: The eternal text editor — Didactic Ersatz Emacs demonstrating immutable
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Ewig - Eternal Didactic Text Editor

The eternal text editor — Didactic Ersatz Emacs demonstrating immutable data-structures and the single-atom architecture.

## Repository
- **Source**: https://github.com/bmorphism/ewig (fork of arximboldi/ewig)
- **Language**: C++ (immer library)
- **Pattern**: Persistent data structures + single atom state

## Core Concept

Ewig demonstrates how to build a text editor using:
1. **Immutable data structures** - All state changes create new versions
2. **Single-atom architecture** - One atom holds the entire application state
3. **Structural sharing** - Efficient memory via shared structure

```cpp
// Single atom state
atom<editor_state> state;

// All mutations are pure transformations
state.update([](editor_state s) {
    return s.insert_char('x');  // Returns new state, doesn't mutate
});
```

## Architecture

```
┌─────────────────────────────────────────────────────┐
│                      Ewig                           │
├─────────────────────────────────────────────────────┤
│                                                     │
│   ┌─────────────────────────────────────────────┐   │
│   │              Single Atom                    │   │
│   │         (immutable editor_state)            │   │
│   └─────────────────────────────────────────────┘   │
│        │                              │             │
│        ▼                              ▼             │
│   ┌─────────┐                    ┌─────────┐       │
│   │ immer   │   structural       │ lager   │       │
│   │ vectors │   sharing          │ cursors │       │
│   └─────────┘                    └─────────┘       │
│                                                     │
└─────────────────────────────────────────────────────┘
```

## Key Libraries

### immer
Persistent immutable data structures for C++:
```cpp
#include <immer/vector.hpp>

immer::vector<char> buffer = {'h', 'e', 'l', 'l', 'o'};
auto new_buffer = buffer.push_back('!');  // O(log n), shares structure