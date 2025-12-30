# r2con Speaker Integration (2016-2025)

Cross-referencing r2con conference speakers with ASI skill ecosystem for binary analysis, reverse engineering, and process tree inspection.

## Data Sources

- **DuckDB**: `~/login_trace.duckdb` with tables `r2con_events`, `r2con_speakers`, `r2con_talks`
- **CSV Exports**: `~/r2con_events.csv`, `~/r2con_speakers.csv`, `~/r2con_talks.csv`
- **Skills Updated**: 17 skills now reference r2con speaker repositories

## Speaker Repository Index

### Core radare2 Team
| Speaker | Handle | GitHub | Specialty |
|---------|--------|--------|-----------|
| Sergi Alvarez | pancake | [trufae](https://github.com/trufae) | radare2 creator, r2pipe, r2ai |
| Anton Kochkov | xvilka | [XVilka](https://github.com/XVilka) | UEFI, radeco, awesome-decompilation |
| Florian Märkl | thestr4ng3r | [thestr4ng3r](https://github.com/thestr4ng3r) | Cutter/Rizin founder |
| condret | condret | [condret](https://github.com/condret) | ESIL core, SIOL I/O, r2ghidra |
| Giovanni Dante Grazioli | wargio | [wargio](https://github.com/wargio) | GSoC mentor, capstone |

### ESIL & Symbolic Execution
| Speaker | Handle | GitHub | Key Repos |
|---------|--------|--------|-----------|
| Chase Kanipe | alkalinesec | [alkalinesec](https://github.com/alkalinesec) | ESILSolve |
| Sylvain Pelissier | Pelissier_S | N/A | ESIL side-channel simulation |
| Abel Valero | skuater | [skuater](https://github.com/skuater) | r2wars, ESIL plugins |

### Frida Integration
| Speaker | Handle | GitHub | Key Repos |
|---------|--------|--------|-----------|
| Ole André Ravnås | oleavr | [oleavr](https://github.com/oleavr) | frida-core, frida-gum, cryptoshark |
| Giovanni Rocca | iGio90 | [iGio90](https://github.com/iGio90) | Dwarf debugger |
| Grant Douglas | hexploitable | [hexploitable](https://github.com/hexploitable) | Clutch, dumpdecrypted |

### Malware & Security
| Speaker | Handle | GitHub | Key Repos |
|---------|--------|--------|-----------|
| Axelle Apvrille | cryptax | [cryptax](https://github.com/cryptax) | droidlysis, APKiD, blutter |
| Tim Blazytko | mr_phrazer | [mrphrazer](https://github.com/mrphrazer) | msynth, mba, Monocle |
| Julien Voisin | jvoisin | [jvoisin](https://github.com/jvoisin) | mat2, php-malware-finder |

### Signatures & Similarity
| Speaker | Handle | GitHub | Key Repos |
|---------|--------|--------|-----------|
| Barton Rhodes | bmorphism | [bmorphism](https://github.com/bmorphism) | Gay.jl colors, r2 Zignatures (2020) |
| swoops | swoops | [swoops](https://github.com/swoops) | libc_zignatures, dr_pebber |
| Fernando Dominguez | FernandoDoming | [FernandoDoming](https://github.com/FernandoDoming) | diaphora |

### Mobile Security (OWASP MSTG)
| Speaker | Handle | GitHub | Key Repos |
|---------|--------|--------|-----------|
| Carlos Holguera | cpholguera | [cpholguera](https://github.com/cpholguera) | OWASP MSTG |
| Eduardo Novella | enovella | [enovella](https://github.com/enovella) | frida-snippets, blutter |
| Francesco Tamagni | mrmacete | [mrmacete](https://github.com/mrmacete) | iOS tools |

### Decompilation & Rust
| Speaker | Handle | GitHub | Key Repos |
|---------|--------|--------|-----------|
| Ahmed Abd El Mawgood | oddcoder | [oddcoder](https://github.com/oddcoder) | RAIR (Radare In Rust) |
| Antide Petit | xarkes | [xarkes](https://github.com/xarkes) | Cutter development |

## Key Organization Repositories

```bash
# Core ecosystems
git clone https://github.com/radareorg/radare2
git clone https://github.com/radareorg/r2ghidra
git clone https://github.com/radareorg/radare2-mcp
git clone https://github.com/rizinorg/rizin
git clone https://github.com/rizinorg/cutter
git clone https://github.com/frida/frida-core

# Speaker tools for process analysis
git clone https://github.com/swoops/libc_zignatures
git clone https://github.com/swoops/dr_pebber
git clone https://github.com/mrphrazer/msynth
git clone https://github.com/cryptax/droidlysis
git clone https://github.com/iGio90/Dwarf
```

## Skills with r2con References

17 skills now include `## r2con Speaker Resources` sections:

| Skill | Domain | Speakers |
|-------|--------|----------|
| reverse-engineering | Binary analysis | All 30+ speakers |
| effective-topos | Flox env | pancake, xvilka, condret |
| mcp-tripartite | MCP orchestration | radare2 as -1 trit |
| persistent-homology | TDA/binary | oddcoder, mr_phrazer |
| gay-mcp | Colors | bmorphism, pancake, swoops |
| bisimulation-game | Dispersal | swoops, bmorphism, condret |
| blackhat-go | Security | oleavr, cryptax, iGio90 |
| kolmogorov-compression | Compression | mr_phrazer, oddcoder |
| gh-interactome | GitHub graph | radareorg, rizinorg, frida |
| discopy | Diagrams | bmorphism, pancake |
| alife | Artificial life | cryptax, iGio90, swoops |
| acsets | Categorical DB | bmorphism, pancake, swoops |
| segal-types | ∞-categories | bmorphism, condret |
| assembly-index | Complexity | oddcoder, mr_phrazer |
| interaction-nets | Graph rewriting | condret, thestr4ng3r |
| chemical-abstract-machine | CHAM | condret, alkalinesec |
| propagators | Constraints | alkalinesec, condret |
| godel-machine | Self-improving | cryptax, unixfreaxjp |

## Process Tree Analysis Perspectives

Each speaker brings unique analysis perspective for `ps aux` output:

| Speaker | Focus | Approach |
|---------|-------|----------|
| **pancake** | Core r2 | `r2 -d pid://PID` attach |
| **condret** | ESIL | Each PID as ESIL context |
| **Pelissier_S** | Side-channel | Timing oracles in args |
| **alkalinesec** | ESILSolve | Symbolic exec on sandbox |
| **iGio90** | r2frida | `frida -U -n 'process'` |
| **cryptax** | Malware | Persistence via watchdogs |
| **bmorphism** | Zignatures | `zg` across process variants |
| **swoops** | dr_pebber | Fake PEB structures |

## Integration with Gay.jl Colors

```julia
using Gay

# Color r2con speakers by specialty
speakers = [
    ("pancake", :core),
    ("condret", :esil),
    ("oleavr", :frida),
    ("cryptax", :malware),
    ("bmorphism", :signatures)
]

for (i, (name, specialty)) in enumerate(speakers)
    color = Gay.color_at(i, seed=0x72636F6E)  # "rcon" as seed
    println("$name ($specialty): $(color.hex)")
end
```

## GF(3) Trit Classification

```
radare2 = -1 (MINUS)  # Analyze, validate, reverse
glass-bead-game = 0   # Navigate concept space
marginalia = +1       # Search indie documentation

Sum: -1 + 0 + 1 = 0 ✓ (GF(3) conserved)
```
