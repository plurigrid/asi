---
name: turing-chemputer
description: Cronin's Turing-complete chemputer for programmable chemical synthesis
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Turing Chemputer Skill: Programmable Chemical Synthesis

**Status**: ✅ Production Ready
**Trit**: 0 (ERGODIC - coordinator)
**Color**: #26D826 (Green)
**Principle**: Chemistry as computation
**Frame**: XDL programs executed on modular hardware

---

## Overview

**Turing Chemputer** coordinates chemical synthesis as program execution. Using XDL (Chemical Description Language), any synthesis protocol becomes an executable program on modular robotic hardware.

1. **XDL**: XML-based chemical programming language
2. **Chempiler**: Compile XDL to hardware instructions
3. **Modular hardware**: Reactors, filters, separators as primitives
4. **Turing completeness**: Loops, conditionals, recursion

## Core Framework

```xml
<!-- XDL: Chemical Description Language -->
<Synthesis>
  <Hardware>
    <Reactor id="reactor1" volume="100 mL"/>
    <Filter id="filter1"/>
    <Separator id="sep1"/>
  </Hardware>
  
  <Procedure>
    <Add reagent="A" vessel="reactor1" amount="10 mmol"/>
    <Add reagent="B" vessel="reactor1" amount="12 mmol"/>
    <HeatChill vessel="reactor1" temp="80 °C" time="2 h"/>
    <Filter from="reactor1" to="filter1"/>
  </Procedure>
</Synthesis>
```

```python
def compile_xdl(xdl: str) -> HardwareInstructions:
    """Chempiler: XDL → executable hardware program."""
    tree = parse_xdl(xdl)
    graph = build_synthesis_graph(tree)
    return optimize_and_schedule(graph)
```

## Key Concepts

### 1. XDL Programming

```python
class XDLProgram:
    def __init__(self):
        self.steps = []
    
    def add(self, reagent: str, vessel: str, amount: str):
        self.steps.append(Add(reagent, vessel, amount))
    
    def heat(self, vessel: str, temp: str, time: str):
        self.steps.append(HeatChill(vessel, temp, time))
    
    def filter(self, from_vessel: str, to_vessel: str):
        self.steps.append(Filter(from_vessel, to_vessel))
    
    def loop(self, times: int, body: list):
        """Turing-complete: iteration."""
        self.steps.append(Loop(