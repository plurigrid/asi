//! # CRDT E-Graph: Rust Implementation
//!
//! A high-performance e-graph implementation with automatic 3-coloring for CRDT merge semantics.
//! Combines conflict-free replicated data types with categorical rewriting theory.
//!
//! ## Design Principles
//!
//! 1. **3-Coloring by Construction**: Color enforcement via rewrite rule structure
//! 2. **Commutative Merge**: Deterministic conflict resolution via Möbius inversion
//! 3. **Content-Addressed**: Fingerprinting enables cache coherence
//! 4. **Operational Semantics**: Based on open games framework (2TDX)

pub mod colors;
pub mod crdt;
pub mod egraph;
pub mod merge;
pub mod patterns;
pub mod verify;

pub use colors::{ColorInfo, ColorType, Polarity};
pub use crdt::{CRDTOp, CRDTState};
pub use egraph::{CRDTEGraph, EClass, ENode, ENodeId};
pub use merge::{CommutativeMerge, MergeContext, MergeResult, MergeStrategy, MobiusInverter};
pub use patterns::{GadgetPattern, LHSPattern, RHSPattern, RewriteRule, RuleSet};
pub use verify::{ThreeColorVerifier, VerificationStats, Saturator, DistributedSaturation};

use std::fmt;

/// Main error type for CRDT e-graph operations
#[derive(Debug, thiserror::Error)]
pub enum CRDTEGraphError {
    #[error("Node not found: {0}")]
    NodeNotFound(String),

    #[error("Class not found: {0}")]
    ClassNotFound(String),

    #[error("Merge failed: {0}")]
    MergeFailed(String),

    #[error("Color constraint violated: {0}")]
    ColorConstraintViolated(String),

    #[error("Rewrite failed: {0}")]
    RewriteFailed(String),

    #[error("Verification failed: {0}")]
    VerificationFailed(String),

    #[error("Invalid CRDT operation: {0}")]
    InvalidCRDTOp(String),
}

pub type Result<T> = std::result::Result<T, CRDTEGraphError>;

/// Global CRDT e-graph version for tracking
pub const VERSION: &str = "0.2.0";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_version() {
        assert_eq!(VERSION, "0.2.0");
    }
}
