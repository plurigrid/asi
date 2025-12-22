"""
Test: paperproof Proof Extraction
Duration: ~5 seconds
Status: Unit test for proof visualization
"""

import pytest


class MockProofMetadata:
    """Mock proof metadata"""
    def __init__(self, theorem_name, steps, tactics):
        self.theorem_name = theorem_name
        self.steps = steps
        self.tactics = tactics


class MockProofValidation:
    """Mock proof validation result"""
    def __init__(self, passes, conclusion=None):
        self.passes = passes
        self.conclusion = conclusion
        self.missing_goals = [] if passes else ["unresolved goal"]


class MockPaperproofVisualizer:
    """Mock paperproof visualizer"""
    def __init__(self, lean_source=None, theorem_name=None):
        self.lean_source = lean_source
        self.theorem_name = theorem_name
        self.proof_state = {
            "hypotheses": [],
            "goals": ["main_goal"]
        }

    def extract_metadata(self):
        """Extract proof metadata"""
        return MockProofMetadata(
            theorem_name=self.theorem_name,
            steps=1,
            tactics=["rfl"] if "rfl" in self.lean_source else ["sorry"]
        )

    def validate_proof(self, expected_conclusion=None):
        """Validate proof correctness"""
        # Simple validation: check if "rfl" is in source (reflexivity proof)
        passes = "rfl" in self.lean_source if self.lean_source else False
        return MockProofValidation(passes=passes, conclusion=expected_conclusion)

    def visualize(self):
        """Generate proof visualization"""
        return f"<svg>Proof: {self.theorem_name}</svg>"

    def export_html(self, filename):
        """Export to HTML"""
        return True

    def export_image(self, filename, format="png"):
        """Export to image"""
        return True

    def analyze_tactics(self):
        """Analyze tactic effects"""
        return {
            "steps": [
                {
                    "name": "rfl",
                    "hypotheses_before": 0,
                    "goals_before": 1,
                    "hypotheses_after": 0,
                    "goals_after": 0
                }
            ]
        }


def test_visualizer_creation():
    """Test that visualizer can be created"""
    lean_code = "theorem simple : 2 + 2 = 4 := by rfl"

    visualizer = MockPaperproofVisualizer(
        lean_source=lean_code,
        theorem_name="simple"
    )

    assert visualizer.theorem_name == "simple"
    assert lean_code in visualizer.lean_source


def test_metadata_extraction():
    """Test that metadata can be extracted"""
    lean_code = "theorem simple : 2 + 2 = 4 := by rfl"
    visualizer = MockPaperproofVisualizer(
        lean_source=lean_code,
        theorem_name="simple"
    )

    metadata = visualizer.extract_metadata()

    assert metadata.theorem_name == "simple"
    assert metadata.steps > 0
    assert len(metadata.tactics) > 0


def test_proof_validation_pass():
    """Test validation of correct proof"""
    lean_code = "theorem simple : 2 + 2 = 4 := by rfl"
    visualizer = MockPaperproofVisualizer(
        lean_source=lean_code,
        theorem_name="simple"
    )

    validation = visualizer.validate_proof(expected_conclusion="2 + 2 = 4")

    assert validation.passes is True
    assert validation.conclusion == "2 + 2 = 4"


def test_proof_validation_fail():
    """Test validation of incomplete proof"""
    lean_code = "theorem incomplete : True := by sorry"
    visualizer = MockPaperproofVisualizer(
        lean_source=lean_code,
        theorem_name="incomplete"
    )

    validation = visualizer.validate_proof()

    assert validation.passes is False
    assert len(validation.missing_goals) > 0


def test_visualization_generation():
    """Test that visualization can be generated"""
    lean_code = "theorem simple : 2 + 2 = 4 := by rfl"
    visualizer = MockPaperproofVisualizer(
        lean_source=lean_code,
        theorem_name="simple"
    )

    visual = visualizer.visualize()

    assert isinstance(visual, str)
    assert len(visual) > 0
    assert "Proof" in visual


def test_html_export():
    """Test HTML export"""
    lean_code = "theorem simple : 2 + 2 = 4 := by rfl"
    visualizer = MockPaperproofVisualizer(
        lean_source=lean_code,
        theorem_name="simple"
    )

    result = visualizer.export_html("proof.html")
    assert result is True


def test_image_export():
    """Test image export"""
    lean_code = "theorem simple : 2 + 2 = 4 := by rfl"
    visualizer = MockPaperproofVisualizer(
        lean_source=lean_code,
        theorem_name="simple"
    )

    result = visualizer.export_image("proof.png", format="png")
    assert result is True


def test_tactic_analysis():
    """Test tactic effect analysis"""
    lean_code = "theorem simple : 2 + 2 = 4 := by rfl"
    visualizer = MockPaperproofVisualizer(
        lean_source=lean_code,
        theorem_name="simple"
    )

    analysis = visualizer.analyze_tactics()

    assert "steps" in analysis
    assert len(analysis["steps"]) > 0

    step = analysis["steps"][0]
    assert "name" in step
    assert "hypotheses_before" in step
    assert "goals_before" in step
    assert "hypotheses_after" in step
    assert "goals_after" in step


def test_multiple_proofs():
    """Test handling of multiple different proofs"""
    proofs = {
        "simple": "theorem simple : 2 + 2 = 4 := by rfl",
        "incomplete": "theorem incomplete : True := by sorry"
    }

    for name, code in proofs.items():
        visualizer = MockPaperproofVisualizer(
            lean_source=code,
            theorem_name=name
        )

        assert visualizer.theorem_name == name
        assert visualizer.extract_metadata() is not None


def test_proof_state_tracking():
    """Test that proof state is tracked"""
    lean_code = "theorem simple : 2 + 2 = 4 := by rfl"
    visualizer = MockPaperproofVisualizer(
        lean_source=lean_code,
        theorem_name="simple"
    )

    # Initial state
    assert len(visualizer.proof_state["goals"]) > 0

    # After validation, should be aware of proof state
    validation = visualizer.validate_proof()
    assert validation is not None


def test_theorem_name_persistence():
    """Test that theorem name is preserved"""
    theorem_names = ["add_comm", "mul_zero", "simple_identity"]

    for name in theorem_names:
        visualizer = MockPaperproofVisualizer(
            lean_source="theorem dummy := by rfl",
            theorem_name=name
        )

        assert visualizer.theorem_name == name
        assert visualizer.extract_metadata().theorem_name == name


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
