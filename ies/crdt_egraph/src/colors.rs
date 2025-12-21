//! Color type system for 3-coloring by construction
//!
//! The three-gadget system enforces colors via rewrite rule structure:
//! - RED (Gadget 1): Forward associative rewrites  (positive polarity)
//! - BLUE (Gadget 2): Backward distributive rewrites (negative polarity)
//! - GREEN (Gadget 3): Verification identity (neutral polarity)

use serde::{Deserialize, Serialize};
use std::fmt;

/// The three colors in the gadget system
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ColorType {
    /// RED: Forward associative rewriting (positive)
    /// Pattern: (a ⊕ b) ⊕ c → a ⊕ (b ⊕ c)
    /// Constraint: Children must be RED or GREEN
    Red,

    /// BLUE: Backward distributive rewriting (negative)
    /// Pattern: a ⊕ (b ⊕ c) → (a ⊕ b) ⊕ c
    /// Constraint: Children must be BLUE or GREEN
    Blue,

    /// GREEN: Verification/Identity (neutral)
    /// Pattern: Identity without structural change
    /// Constraint: Can apply to any node
    /// Effect: Absorbs colors - certifies equivalence
    Green,
}

impl ColorType {
    /// Check if this color is compatible with a child color
    ///
    /// RED nodes can have RED or GREEN children
    /// BLUE nodes can have BLUE or GREEN children
    /// GREEN nodes can have any color children
    pub fn is_compatible_with(&self, child: ColorType) -> bool {
        match (self, child) {
            // RED cannot have BLUE children
            (ColorType::Red, ColorType::Blue) => false,
            // BLUE cannot have RED children
            (ColorType::Blue, ColorType::Red) => false,
            // GREEN can be child of anything
            // GREEN can have any children
            _ => true,
        }
    }

    /// Get the dominant color in a merge (higher priority)
    ///
    /// Priority: RED > BLUE > GREEN
    /// Used in congruence closure to determine e-class color
    pub fn merge_with(&self, other: ColorType) -> ColorType {
        match (self, other) {
            // RED dominates everything
            (ColorType::Red, _) | (_, ColorType::Red) => ColorType::Red,
            // BLUE dominates GREEN
            (ColorType::Blue, _) | (_, ColorType::Blue) => ColorType::Blue,
            // GREEN is lowest priority
            (ColorType::Green, ColorType::Green) => ColorType::Green,
        }
    }

    /// Convert to string representation
    pub fn as_str(&self) -> &'static str {
        match self {
            ColorType::Red => "RED",
            ColorType::Blue => "BLUE",
            ColorType::Green => "GREEN",
        }
    }

    /// All color variants for iteration
    pub fn all() -> [ColorType; 3] {
        [ColorType::Red, ColorType::Blue, ColorType::Green]
    }
}

impl fmt::Display for ColorType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Girard polarity for operations
/// Used to classify operations as constructive (+), destructive (-), or neutral (0)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Polarity {
    /// Positive: Forward/constructive operations (building structure)
    /// Associated with RED color
    Positive,

    /// Negative: Backward/destructive operations (unbuilding structure)
    /// Associated with BLUE color
    Negative,

    /// Neutral: Identity and verification operations (no change)
    /// Associated with GREEN color
    Neutral,
}

impl Polarity {
    /// Convert polarity to its associated color
    pub fn to_color(&self) -> ColorType {
        match self {
            Polarity::Positive => ColorType::Red,
            Polarity::Negative => ColorType::Blue,
            Polarity::Neutral => ColorType::Green,
        }
    }

    /// Convert color back to polarity
    pub fn from_color(color: ColorType) -> Self {
        match color {
            ColorType::Red => Polarity::Positive,
            ColorType::Blue => Polarity::Negative,
            ColorType::Green => Polarity::Neutral,
        }
    }

    /// Get opposite polarity (dual in open games sense)
    pub fn opposite(&self) -> Polarity {
        match self {
            Polarity::Positive => Polarity::Negative,
            Polarity::Negative => Polarity::Positive,
            Polarity::Neutral => Polarity::Neutral,
        }
    }

    /// Check if two polarities are compatible
    /// Positive and negative can coexist in dual manner
    /// Neutral is compatible with everything
    pub fn is_compatible_with(&self, other: Polarity) -> bool {
        matches!(
            (self, other),
            (Polarity::Neutral, _)
                | (_, Polarity::Neutral)
                | (Polarity::Positive, Polarity::Negative)
                | (Polarity::Negative, Polarity::Positive)
        )
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            Polarity::Positive => "positive",
            Polarity::Negative => "negative",
            Polarity::Neutral => "neutral",
        }
    }
}

impl fmt::Display for Polarity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Color information with timestamp
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ColorInfo {
    pub color: ColorType,
    pub polarity: Polarity,
    pub gadget_id: String, // Which gadget applied this color
    pub timestamp: chrono::DateTime<chrono::Utc>,
}

impl ColorInfo {
    /// Create new color info
    pub fn new(color: ColorType, polarity: Polarity, gadget_id: String) -> Self {
        Self {
            color,
            polarity,
            gadget_id,
            timestamp: chrono::Utc::now(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_color_compatibility() {
        assert!(ColorType::Red.is_compatible_with(ColorType::Green));
        assert!(ColorType::Red.is_compatible_with(ColorType::Red));
        assert!(!ColorType::Red.is_compatible_with(ColorType::Blue));

        assert!(ColorType::Blue.is_compatible_with(ColorType::Green));
        assert!(ColorType::Blue.is_compatible_with(ColorType::Blue));
        assert!(!ColorType::Blue.is_compatible_with(ColorType::Red));

        assert!(ColorType::Green.is_compatible_with(ColorType::Red));
        assert!(ColorType::Green.is_compatible_with(ColorType::Blue));
        assert!(ColorType::Green.is_compatible_with(ColorType::Green));
    }

    #[test]
    fn test_color_merge() {
        assert_eq!(
            ColorType::Red.merge_with(ColorType::Blue),
            ColorType::Red
        );
        assert_eq!(
            ColorType::Blue.merge_with(ColorType::Green),
            ColorType::Blue
        );
        assert_eq!(
            ColorType::Green.merge_with(ColorType::Green),
            ColorType::Green
        );
    }

    #[test]
    fn test_polarity_conversion() {
        assert_eq!(Polarity::Positive.to_color(), ColorType::Red);
        assert_eq!(Polarity::Negative.to_color(), ColorType::Blue);
        assert_eq!(Polarity::Neutral.to_color(), ColorType::Green);
    }

    #[test]
    fn test_polarity_opposite() {
        assert_eq!(Polarity::Positive.opposite(), Polarity::Negative);
        assert_eq!(Polarity::Negative.opposite(), Polarity::Positive);
        assert_eq!(Polarity::Neutral.opposite(), Polarity::Neutral);
    }

    #[test]
    fn test_polarity_compatibility() {
        assert!(Polarity::Positive.is_compatible_with(Polarity::Negative));
        assert!(Polarity::Neutral.is_compatible_with(Polarity::Positive));
        assert!(Polarity::Neutral.is_compatible_with(Polarity::Negative));
    }
}
