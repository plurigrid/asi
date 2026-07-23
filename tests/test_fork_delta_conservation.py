import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.fork_delta_conservation import classify_delta, recommendation


class ForkDeltaConservationTests(unittest.TestCase):
    def test_upstream_sync_gap_mathlib_arithmetic(self):
        left = {"ahead_by": 0, "behind_by": 3915}
        right = {"ahead_by": 0, "behind_by": 25605}
        pairwise = {"ahead_by": 21690, "behind_by": 0}
        self.assertEqual(classify_delta(left, right, pairwise), "upstream-sync-gap")
        self.assertIn("Do not treat", recommendation("upstream-sync-gap"))

    def test_same_upstream_snapshot(self):
        left = {"ahead_by": 0, "behind_by": 12}
        right = {"ahead_by": 0, "behind_by": 12}
        pairwise = {"ahead_by": 0, "behind_by": 0}
        self.assertEqual(classify_delta(left, right, pairwise), "same-upstream-snapshot")

    def test_original_work_present(self):
        left = {"ahead_by": 3, "behind_by": 0}
        right = {"ahead_by": 0, "behind_by": 0}
        pairwise = {"ahead_by": 3, "behind_by": 0}
        self.assertEqual(classify_delta(left, right, pairwise), "original-work-present")

    def test_mixed_upstream_and_original(self):
        left = {"ahead_by": 3, "behind_by": 5}
        right = {"ahead_by": 0, "behind_by": 10}
        pairwise = {"ahead_by": 8, "behind_by": 0}
        self.assertEqual(classify_delta(left, right, pairwise), "mixed-upstream-and-original")


if __name__ == "__main__":
    unittest.main()
