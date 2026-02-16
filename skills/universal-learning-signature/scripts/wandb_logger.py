#!/usr/bin/env python3
"""
Weights & Biases Integration for Universal Learning Signature Framework

Provides comprehensive experiment tracking, reproducibility logging, and
visualization support for validation tests and measurements.
"""

import json
import os
from datetime import datetime
from typing import Any, Dict, Optional, Tuple
import warnings

try:
    import wandb
    WANDB_AVAILABLE = True
except ImportError:
    WANDB_AVAILABLE = False
    warnings.warn("Weights & Biases not installed. Install with: pip install wandb")


class WANDBTracker:
    """
    Comprehensive W&B experiment tracker for Universal Learning Signature framework.

    Features:
    - Automatic experiment logging
    - Measurement tracking with confidence scores
    - Reproducibility documentation
    - Artifact versioning
    - Hyperparameter tracking
    """

    def __init__(
        self,
        project: str = "universal-learning-signature",
        entity: Optional[str] = None,
        tags: Optional[list] = None,
        notes: Optional[str] = None,
        offline: bool = False,
    ):
        """
        Initialize W&B tracker.

        Args:
            project: W&B project name
            entity: W&B entity (team/username)
            tags: Experiment tags for filtering
            notes: Experiment notes
            offline: Run offline mode (no W&B server)
        """
        self.project = project
        self.entity = entity
        self.tags = tags or []
        self.notes = notes
        self.offline = offline
        self.run = None
        self.enabled = WANDB_AVAILABLE

    def start_run(
        self,
        name: str,
        config: Optional[Dict[str, Any]] = None,
        **kwargs
    ) -> Optional[Any]:
        """
        Start a new W&B run.

        Args:
            name: Run name
            config: Hyperparameter configuration
            **kwargs: Additional wandb.init() arguments

        Returns:
            W&B run object or None if disabled
        """
        if not self.enabled:
            return None

        try:
            self.run = wandb.init(
                project=self.project,
                entity=self.entity,
                name=name,
                config=config or {},
                tags=self.tags,
                notes=self.notes,
                mode="offline" if self.offline else "online",
                **kwargs
            )
            return self.run
        except Exception as e:
            warnings.warn(f"Failed to start W&B run: {e}")
            self.enabled = False
            return None

    def log_measurement(
        self,
        domain: str,
        measurement_type: str,
        value: float,
        confidence: float,
        expected: Optional[float] = None,
        notes: str = "",
        step: Optional[int] = None,
    ) -> None:
        """
        Log a measurement with confidence score.

        Args:
            domain: Domain name (Topobench, GitHub, IES)
            measurement_type: Type (D, f, H₁)
            value: Measured value
            confidence: Confidence score [0, 1]
            expected: Expected value (for comparison)
            notes: Additional notes
            step: Step counter
        """
        if not self.enabled or not self.run:
            return

        try:
            log_data = {
                f"{domain}/{measurement_type}": value,
                f"{domain}/{measurement_type}_confidence": confidence,
            }

            if expected is not None:
                log_data[f"{domain}/{measurement_type}_expected"] = expected
                log_data[f"{domain}/{measurement_type}_error"] = abs(value - expected)

            if notes:
                log_data[f"{domain}/{measurement_type}_notes"] = notes

            self.run.log(log_data, step=step)
        except Exception as e:
            warnings.warn(f"Failed to log measurement: {e}")

    def log_test_result(
        self,
        test_name: str,
        status: str,  # PASS, FAIL, PARTIAL
        metrics: Dict[str, Any],
        step: Optional[int] = None,
    ) -> None:
        """
        Log test results with associated metrics.

        Args:
            test_name: Test name
            status: Test status (PASS/FAIL/PARTIAL)
            metrics: Test metrics dictionary
            step: Step counter
        """
        if not self.enabled or not self.run:
            return

        try:
            status_value = {"PASS": 1.0, "PARTIAL": 0.5, "FAIL": 0.0}.get(status, 0.0)

            log_data = {
                f"tests/{test_name}/status": status_value,
                f"tests/{test_name}/status_text": status,
                **{f"tests/{test_name}/{k}": v for k, v in metrics.items()}
            }

            self.run.log(log_data, step=step)
        except Exception as e:
            warnings.warn(f"Failed to log test result: {e}")

    def log_model_checkpoint(
        self,
        path: str,
        name: str = "model",
        alias: str = "best",
    ) -> None:
        """
        Log a model checkpoint as artifact.

        Args:
            path: Path to model file
            name: Artifact name
            alias: Artifact alias (best/latest)
        """
        if not self.enabled or not self.run:
            return

        try:
            artifact = wandb.Artifact(name, type="model")
            artifact.add_file(path)
            self.run.log_artifact(artifact, aliases=[alias])
        except Exception as e:
            warnings.warn(f"Failed to log artifact: {e}")

    def log_table(
        self,
        table_name: str,
        data: Dict[str, list],
    ) -> None:
        """
        Log a results table.

        Args:
            table_name: Table name
            data: Dictionary of column_name: [values]
        """
        if not self.enabled or not self.run:
            return

        try:
            table = wandb.Table(data=list(zip(*data.values())), columns=list(data.keys()))
            self.run.log({table_name: table})
        except Exception as e:
            warnings.warn(f"Failed to log table: {e}")

    def log_summary(self, summary: Dict[str, Any]) -> None:
        """
        Log summary metrics.

        Args:
            summary: Summary metrics dictionary
        """
        if not self.enabled or not self.run:
            return

        try:
            for key, value in summary.items():
                self.run.summary[key] = value
        except Exception as e:
            warnings.warn(f"Failed to log summary: {e}")

    def finish(self) -> None:
        """Finish the W&B run."""
        if self.enabled and self.run:
            try:
                self.run.finish()
            except Exception as e:
                warnings.warn(f"Failed to finish W&B run: {e}")

    def __enter__(self):
        """Context manager entry."""
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """Context manager exit."""
        self.finish()


def create_reproducibility_log() -> Dict[str, Any]:
    """
    Create reproducibility documentation log.

    Returns:
        Dictionary with system, code, and data information
    """
    import platform
    import sys
    from datetime import datetime

    return {
        "timestamp": datetime.now().isoformat(),
        "platform": platform.platform(),
        "python_version": f"{sys.version_info.major}.{sys.version_info.minor}.{sys.version_info.micro}",
        "python_executable": sys.executable,
        "working_directory": os.getcwd(),
        "environment_vars": {
            "PYTHONHASHSEED": os.environ.get("PYTHONHASHSEED", "not set"),
            "PYTHONPATH": os.environ.get("PYTHONPATH", "not set"),
        },
    }


def setup_wandb_environment() -> None:
    """
    Setup W&B environment for optimal reproducibility.

    - Disables analytics
    - Sets up offline mode if needed
    - Configures reproducibility settings
    """
    os.environ["WANDB_SILENT"] = "true"

    # Enable reproducibility
    if "PYTHONHASHSEED" not in os.environ:
        os.environ["PYTHONHASHSEED"] = "0"


# Example usage demonstration
if __name__ == "__main__":
    print("Weights & Biases Integration Module")
    print("====================================\n")

    # Check availability
    if WANDB_AVAILABLE:
        print("✓ W&B is available")
        print(f"  W&B version: {wandb.__version__}")
    else:
        print("✗ W&B is not installed")
        print("  Install with: pip install wandb")

    # Show initialization example
    print("\nExample usage:")
    print("""
    tracker = WANDBTracker(
        project="universal-learning-signature",
        tags=["measurement-procedures", "validation"],
        notes="Topobench H₁ = 0 validation"
    )

    tracker.start_run("topobench_validation_run_1")

    # Log measurement
    tracker.log_measurement(
        domain="Topobench",
        measurement_type="H1",
        value=0.0,
        confidence=0.95,
        expected=0.0,
        notes="MINUS polarity variant"
    )

    # Log test results
    tracker.log_test_result(
        test_name="h1_convergence",
        status="PASS",
        metrics={"accuracy": 1.0}
    )

    # Log summary
    tracker.log_summary({
        "overall_confidence": 0.95,
        "domain": "Topobench"
    })

    tracker.finish()
    """)
