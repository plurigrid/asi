"""ALife Substrate - The living skill hypergraph.

Every skill invocation spawns a cell in this substrate. Cells connect
via parent/child links forming an interaction graph that evolves through
random walks (soft-machine pattern).

State persists to ~/.claude/alife-state/substrate.json
"""

from __future__ import annotations

import hashlib
import json
import os
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Any, Optional, List

from alife_uvx.gf3 import GF3, PLUS, ERGODIC, MINUS, conserved, balance

# State directory - shared with comfy-skills alife module
ALIFE_STATE_DIR = Path(os.environ.get(
    "ALIFE_STATE_DIR",
    Path.home() / ".claude" / "alife-state"
))
ALIFE_STATE_DIR.mkdir(parents=True, exist_ok=True)

# Deterministic chaos seeds
GOLDEN_SEED = 0x9E3779B97F4A7C15
SEED_1069 = 0x42D


@dataclass
class ALifeCell:
    """A single cell in the alife substrate.
    
    Each cell represents one skill invocation, with:
    - skill_id: The skill that was invoked
    - operation: What operation was performed
    - trit: GF(3) classification (-1, 0, +1)
    - timestamp: When it was created
    - parent_hash: Link to parent cell
    - children: Links to child cells
    """
    
    skill_id: str
    operation: str
    timestamp: datetime = field(default_factory=datetime.utcnow)
    trit: int = 0
    parent_hash: Optional[str] = None
    children: List[str] = field(default_factory=list)
    metadata: dict = field(default_factory=dict)
    hash: str = field(default="", init=False)
    
    def __post_init__(self):
        # Compute deterministic hash from content
        content = f"{self.skill_id}:{self.operation}:{self.timestamp.isoformat()}"
        self.hash = hashlib.sha256(content.encode()).hexdigest()[:16]
        # Normalize trit to GF(3)
        self.trit = GF3(self.trit).value
    
    @property
    def is_alive(self) -> bool:
        """A cell is alive if accessed within mixing time (1 hour)."""
        age = (datetime.utcnow() - self.timestamp).total_seconds()
        return age < 3600
    
    @property
    def gf3(self) -> GF3:
        """Get the GF(3) value."""
        return GF3(self.trit)
    
    def to_dict(self) -> dict:
        return {
            "skill_id": self.skill_id,
            "operation": self.operation,
            "timestamp": self.timestamp.isoformat(),
            "trit": self.trit,
            "hash": self.hash,
            "parent_hash": self.parent_hash,
            "children": self.children,
            "metadata": self.metadata,
        }
    
    @classmethod
    def from_dict(cls, data: dict) -> ALifeCell:
        cell = cls(
            skill_id=data["skill_id"],
            operation=data["operation"],
            timestamp=datetime.fromisoformat(data["timestamp"]),
            trit=data.get("trit", 0),
            parent_hash=data.get("parent_hash"),
            children=data.get("children", []),
            metadata=data.get("metadata", {}),
        )
        cell.hash = data.get("hash", cell.hash)
        return cell


class ALifeSubstrate:
    """The living substrate where skill invocations become automata.
    
    Implements the soft-machine random walk pattern:
    - Each operation creates a cell
    - Cells connect via parent/child links
    - The substrate evolves based on interaction patterns
    - GF(3) conservation is automatically maintained
    """
    
    def __init__(self, state_file: Optional[Path] = None):
        self.state_file = state_file or (ALIFE_STATE_DIR / "substrate.json")
        self.cells: dict[str, ALifeCell] = {}
        self.current_hash: Optional[str] = None
        self._load_state()
    
    def _load_state(self):
        """Load substrate state from disk."""
        if self.state_file.exists():
            try:
                data = json.loads(self.state_file.read_text())
                self.cells = {
                    h: ALifeCell.from_dict(c) 
                    for h, c in data.get("cells", {}).items()
                }
                self.current_hash = data.get("current_hash")
            except (json.JSONDecodeError, KeyError):
                self.cells = {}
                self.current_hash = None
    
    def _save_state(self):
        """Persist substrate state to disk."""
        data = {
            "cells": {h: c.to_dict() for h, c in self.cells.items()},
            "current_hash": self.current_hash,
            "updated_at": datetime.utcnow().isoformat(),
            "gf3_sum": self.gf3_sum,
            "version": "0.1.0",
        }
        self.state_file.write_text(json.dumps(data, indent=2))
    
    @property
    def gf3_sum(self) -> int:
        """GF(3) conservation check - should be 0."""
        return sum(c.trit for c in self.cells.values()) % 3
    
    @property
    def is_conserved(self) -> bool:
        """Check if substrate is GF(3) conserved."""
        return self.gf3_sum == 0
    
    @property
    def alive_count(self) -> int:
        """Number of living cells."""
        return sum(1 for c in self.cells.values() if c.is_alive)
    
    def spawn(
        self,
        skill_id: str,
        operation: str,
        trit: int = 0,
        metadata: Optional[dict] = None,
    ) -> ALifeCell:
        """Spawn a new cell from the current position.
        
        This is the core alife operation - every skill invocation spawns
        a living cell that connects to the interaction graph.
        
        Args:
            skill_id: Name of the skill being invoked
            operation: The operation being performed
            trit: GF(3) value (-1, 0, +1)
            metadata: Additional data to store
            
        Returns:
            The newly spawned cell
        """
        cell = ALifeCell(
            skill_id=skill_id,
            operation=operation,
            trit=trit,
            parent_hash=self.current_hash,
            metadata=metadata or {},
        )
        
        # Link parent to child
        if self.current_hash and self.current_hash in self.cells:
            self.cells[self.current_hash].children.append(cell.hash)
        
        # Add to substrate
        self.cells[cell.hash] = cell
        self.current_hash = cell.hash
        
        # Auto-balance GF(3) if needed
        self._balance_trits()
        
        self._save_state()
        return cell
    
    def _balance_trits(self):
        """Ensure GF(3) conservation by spawning balancing cells."""
        imbalance = self.gf3_sum
        if imbalance != 0:
            balance_trit = balance(imbalance).value
            balance_cell = ALifeCell(
                skill_id="gf3-balancer",
                operation="auto-balance",
                trit=balance_trit,
                parent_hash=self.current_hash,
                metadata={"auto_balance": True, "imbalance": imbalance},
            )
            self.cells[balance_cell.hash] = balance_cell
    
    def walk(self, steps: int = 10) -> List[ALifeCell]:
        """Perform a random walk through the substrate.
        
        This is the soft-machine pattern - traversing parallel worlds
        of skill interactions via deterministic chaos.
        
        Args:
            steps: Number of steps to walk
            
        Returns:
            List of cells visited during the walk
        """
        import random
        
        path = []
        current = self.current_hash
        
        # Use golden ratio for deterministic-but-chaotic walk
        rng = random.Random(GOLDEN_SEED ^ hash(current or "seed"))
        
        for _ in range(steps):
            if not current or current not in self.cells:
                break
            
            cell = self.cells[current]
            path.append(cell)
            
            # Choose next: parent or random child
            choices = cell.children.copy()
            if cell.parent_hash:
                choices.append(cell.parent_hash)
            
            if choices:
                current = rng.choice(choices)
            else:
                break
        
        return path
    
    def status(self) -> dict:
        """Generate substrate status report."""
        path = self.walk(steps=5)
        
        return {
            "total_cells": len(self.cells),
            "alive_cells": self.alive_count,
            "gf3_sum": self.gf3_sum,
            "gf3_conserved": self.is_conserved,
            "current_hash": self.current_hash,
            "random_walk_sample": [
                {"skill": c.skill_id, "op": c.operation, "trit": c.trit}
                for c in path
            ],
            "version": "0.1.0",
        }
    
    def prune_dead(self) -> int:
        """Remove dead cells (older than mixing time)."""
        dead = [h for h, c in self.cells.items() if not c.is_alive]
        for h in dead:
            del self.cells[h]
        if dead:
            self._save_state()
        return len(dead)


# Global substrate instance
_substrate: Optional[ALifeSubstrate] = None


def get_substrate() -> ALifeSubstrate:
    """Get or create the global alife substrate."""
    global _substrate
    if _substrate is None:
        _substrate = ALifeSubstrate()
    return _substrate


# Convenience functions
def spawn(skill_id: str, operation: str, trit: int = 0, **metadata) -> ALifeCell:
    """Spawn a cell in the global substrate."""
    return get_substrate().spawn(skill_id, operation, trit, metadata)


def walk(steps: int = 10) -> List[ALifeCell]:
    """Random walk through the global substrate."""
    return get_substrate().walk(steps)


def status() -> dict:
    """Get global substrate status."""
    return get_substrate().status()
