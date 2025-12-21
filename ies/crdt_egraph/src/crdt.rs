//! CRDT types and operations
//!
//! This module defines the six core CRDT types implemented in Julia and
//! provides Rust equivalents for e-graph integration:
//!
//! 1. TextCRDT: Conflict-free text editing (fractional indexing)
//! 2. JSONCRDT: Last-Write-Wins nested documents
//! 3. GCounter: Grow-only counter
//! 4. PNCounter: Positive-Negative counter
//! 5. ORSet: Observed-Remove Set
//! 6. TAPStateCRDT: Balanced ternary state machine

use crate::colors::{ColorType, Polarity};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

/// Unique identifier for a CRDT operation
pub type OpId = String;

/// Agent/replica identifier
pub type AgentId = String;

/// Logical timestamp (Lamport clock)
pub type Timestamp = u64;

/// Vector clock for causality tracking
pub type VectorClock = BTreeMap<AgentId, Timestamp>;

/// Fingerprint (content-addressed hash)
pub type Fingerprint = u64;

/// Union of all CRDT operation types
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CRDTOp {
    Text(TextOp),
    JSON(JSONOp),
    Counter(CounterOp),
    Set(SetOp),
    State(StateOp),
}

impl CRDTOp {
    /// Get the operation type name
    pub fn op_type(&self) -> &'static str {
        match self {
            CRDTOp::Text(_) => "text",
            CRDTOp::JSON(_) => "json",
            CRDTOp::Counter(_) => "counter",
            CRDTOp::Set(_) => "set",
            CRDTOp::State(_) => "state",
        }
    }

    /// Get polarity of this operation
    pub fn polarity(&self) -> Polarity {
        match self {
            CRDTOp::Text(op) => op.polarity(),
            CRDTOp::JSON(op) => op.polarity(),
            CRDTOp::Counter(op) => op.polarity(),
            CRDTOp::Set(op) => op.polarity(),
            CRDTOp::State(op) => op.polarity(),
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// TextCRDT: Conflict-free collaborative text editing
// ═══════════════════════════════════════════════════════════════════════════════

/// Text operation using fractional indexing
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TextOp {
    /// Insert character at fractional position
    Insert {
        position: f64,
        character: char,
        op_id: OpId,
    },
    /// Delete character at position (tombstone)
    Delete { position: f64, op_id: OpId },
}

impl TextOp {
    pub fn polarity(&self) -> Polarity {
        match self {
            TextOp::Insert { .. } => Polarity::Positive,
            TextOp::Delete { .. } => Polarity::Negative,
        }
    }

    pub fn op_id(&self) -> &str {
        match self {
            TextOp::Insert { op_id, .. } | TextOp::Delete { op_id, .. } => op_id,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// JSONCRDT: Last-Write-Wins nested documents
// ═══════════════════════════════════════════════════════════════════════════════

/// JSON operation (Last-Write-Wins)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum JSONOp {
    /// Set value at path with timestamp
    Set {
        path: Vec<String>,
        value: serde_json::Value,
        timestamp: Timestamp,
    },
    /// Delete value at path
    Delete { path: Vec<String>, timestamp: Timestamp },
}

impl JSONOp {
    pub fn polarity(&self) -> Polarity {
        match self {
            JSONOp::Set { .. } => Polarity::Positive,
            JSONOp::Delete { .. } => Polarity::Negative,
        }
    }

    pub fn timestamp(&self) -> Timestamp {
        match self {
            JSONOp::Set { timestamp, .. } | JSONOp::Delete { timestamp, .. } => *timestamp,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// Counter CRDTs: Numerical values
// ═══════════════════════════════════════════════════════════════════════════════

/// Counter operation (GCounter or PNCounter)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CounterOp {
    /// Increment (GCounter or PNCounter increment side)
    Increment {
        agent: AgentId,
        amount: i64,
    },
    /// Decrement (PNCounter only)
    Decrement {
        agent: AgentId,
        amount: i64,
    },
}

impl CounterOp {
    pub fn polarity(&self) -> Polarity {
        match self {
            CounterOp::Increment { .. } => Polarity::Positive,
            CounterOp::Decrement { .. } => Polarity::Negative,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// ORSet: Observed-Remove Set
// ═══════════════════════════════════════════════════════════════════════════════

/// Set operation (element with unique tag)
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SetTag {
    pub agent: AgentId,
    pub timestamp: Timestamp,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SetOp {
    /// Add element with tag to set
    Add {
        element: String,
        tag: SetTag,
    },
    /// Remove tagged element from set
    Remove { element: String, tag: SetTag },
}

impl SetOp {
    pub fn polarity(&self) -> Polarity {
        match self {
            SetOp::Add { .. } => Polarity::Positive,
            SetOp::Remove { .. } => Polarity::Negative,
        }
    }

    pub fn element(&self) -> &str {
        match self {
            SetOp::Add { element, .. } | SetOp::Remove { element, .. } => element,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// TAPStateCRDT: Ternary state machine
// ═══════════════════════════════════════════════════════════════════════════════

/// Balanced ternary state (-1, 0, +1)
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum TAPState {
    /// Backfill state (-1): Preparing/backfilling data
    Backfill = -1,
    /// Verify state (0): Neutral/verified state
    Verify = 0,
    /// Live state (+1): Active/live operation
    Live = 1,
}

impl TAPState {
    /// Convert to integer representation
    pub fn as_i8(&self) -> i8 {
        match self {
            TAPState::Backfill => -1,
            TAPState::Verify => 0,
            TAPState::Live => 1,
        }
    }

    /// Create from integer
    pub fn from_i8(val: i8) -> Option<Self> {
        match val {
            -1 => Some(TAPState::Backfill),
            0 => Some(TAPState::Verify),
            1 => Some(TAPState::Live),
            _ => None,
        }
    }

    /// Higher state wins in merge
    pub fn merge_with(&self, other: TAPState) -> TAPState {
        match (self.as_i8(), other.as_i8()) {
            (a, b) if a >= b => *self,
            _ => other,
        }
    }
}

/// State machine operation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum StateOp {
    /// Transition to new state
    Transition {
        to_state: TAPState,
        timestamp: Timestamp,
    },
}

impl StateOp {
    pub fn polarity(&self) -> Polarity {
        match self {
            StateOp::Transition { to_state, .. } => match to_state {
                TAPState::Live => Polarity::Positive,
                TAPState::Backfill => Polarity::Negative,
                TAPState::Verify => Polarity::Neutral,
            },
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// CRDT State: Unified state representation
// ═══════════════════════════════════════════════════════════════════════════════

/// Complete CRDT state (result of applying operations)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CRDTState {
    pub op_id: OpId,
    pub agent_id: AgentId,
    pub vector_clock: VectorClock,
    pub fingerprint: Fingerprint,
    pub color: ColorType,
    pub operations: Vec<CRDTOp>,
    pub timestamp: chrono::DateTime<chrono::Utc>,
}

impl CRDTState {
    /// Create new CRDT state
    pub fn new(op_id: OpId, agent_id: AgentId, operations: Vec<CRDTOp>) -> Self {
        Self {
            op_id,
            agent_id,
            vector_clock: Default::default(),
            fingerprint: compute_fingerprint(&operations),
            color: ColorType::Green,
            operations,
            timestamp: chrono::Utc::now(),
        }
    }

    /// Get dominant polarity from all operations
    pub fn dominant_polarity(&self) -> Polarity {
        let mut pos = 0;
        let mut neg = 0;
        let mut neu = 0;

        for op in &self.operations {
            match op.polarity() {
                Polarity::Positive => pos += 1,
                Polarity::Negative => neg += 1,
                Polarity::Neutral => neu += 1,
            }
        }

        match (pos, neg, neu) {
            (p, n, _) if p > n => Polarity::Positive,
            (p, n, _) if n > p => Polarity::Negative,
            _ => Polarity::Neutral,
        }
    }

    /// Set vector clock value
    pub fn set_clock(&mut self, agent: AgentId, timestamp: Timestamp) {
        self.vector_clock.insert(agent, timestamp);
    }
}

/// Compute FNV-1a fingerprint for operations
fn compute_fingerprint(operations: &[CRDTOp]) -> Fingerprint {
    const FNV_PRIME: u64 = 1099511628211;
    const FNV_OFFSET: u64 = 14695981039346656037;

    let mut hash = FNV_OFFSET;

    for op in operations {
        let op_type = op.op_type();
        for byte in op_type.as_bytes() {
            hash = hash.wrapping_mul(FNV_PRIME);
            hash ^= *byte as u64;
        }
    }

    hash
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_crdt_op_polarity() {
        let insert = CRDTOp::Text(TextOp::Insert {
            position: 0.0,
            character: 'a',
            op_id: "op1".to_string(),
        });
        assert_eq!(insert.polarity(), Polarity::Positive);

        let delete = CRDTOp::Text(TextOp::Delete {
            position: 0.0,
            op_id: "op2".to_string(),
        });
        assert_eq!(delete.polarity(), Polarity::Negative);
    }

    #[test]
    fn test_tap_state_merge() {
        assert_eq!(
            TAPState::Backfill.merge_with(TAPState::Live),
            TAPState::Live
        );
        assert_eq!(
            TAPState::Live.merge_with(TAPState::Verify),
            TAPState::Live
        );
        assert_eq!(
            TAPState::Verify.merge_with(TAPState::Verify),
            TAPState::Verify
        );
    }

    #[test]
    fn test_counter_op() {
        let inc = CounterOp::Increment {
            agent: "agent1".to_string(),
            amount: 5,
        };
        assert_eq!(inc.polarity(), Polarity::Positive);

        let dec = CounterOp::Decrement {
            agent: "agent1".to_string(),
            amount: 2,
        };
        assert_eq!(dec.polarity(), Polarity::Negative);
    }
}
