"""Regression cases for live skill discovery, YAML parsing, and merge debris."""
import contextlib
import importlib.util
import io
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "check_skill_integrity", ROOT / "scripts/check_skill_integrity.py")
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)
GOOD = "---\nname: example\ndescription: A valid skill\n---\n# Example\n"


class IntegrityTests(unittest.TestCase):
    def test_valid_yaml_and_markdown(self):
        self.assertEqual([], check.inspect_text(GOOD + "\n---\nBody\n"))
        self.assertEqual([], check.inspect_text(GOOD.replace("\n", "\r\n")))
        self.assertEqual([], check.inspect_text(
            "---\nname: example\ndescription: >\n  Folded: text\nmetadata:\n  nested: [1, 2]\n---\n"))

    def test_body_and_fenced_conflicts_are_not_ignored(self):
        for debris in ("<<<<<<< HEAD\na\n=======\nb\n>>>>>>> origin/main",
                       "````text\n<<<<<<< HEAD\n````", "=======", "||||||| base",
                       "<<<<<<<< ours\nx\n========\ny\n>>>>>>>> theirs"):
            with self.subTest(debris=debris):
                self.assertTrue(check.inspect_text(GOOD + debris))

    def test_embedded_markers_even_in_parseable_yaml(self):
        for value in ("example <<<<<<< HEAD", "'text >>>>>>> origin/main'",
                      "'text ||||||| base'"):
            with self.subTest(value=value):
                self.assertTrue(any("merge marker" in e for e in check.inspect_text(
                    GOOD.replace("name: example", "name: " + value))))

    def test_separator_folded_into_yaml_scalar(self):
        self.assertTrue(any("merge marker" in e for e in check.inspect_text(
            GOOD.replace("name: example", "name: example ======="))))

    def test_normal_markdown_is_not_a_marker(self):
        self.assertEqual([], check.inspect_text(
            GOOD + "Title\n=====\n`a < b` and `x >> 2`\n> quotation\n"))

    def test_missing_or_unclosed_frontmatter(self):
        for text in ("", "# Title", "---\nname: a", "---not-a-delimiter\n---\n"):
            with self.subTest(text=text):
                self.assertTrue(check.inspect_text(text))

    def test_yaml_syntax_type_and_unsafe_tags(self):
        for fm in ("name: a\ndescription: [broken", "- not-a-mapping", "",
                   "name: a\ndescription: !!python/object:builtins.object {}",
                   "name: 42\ndescription: valid", "name: a\ndescription: ''"):
            with self.subTest(fm=fm):
                self.assertTrue(check.inspect_text("---\n" + fm + "\n---\n"))

    def test_duplicate_keys_and_yaml_merge(self):
        for fm in ("name: a\nname: b\ndescription: valid",
                   "name: a\ndescription: valid\nmetadata: {x: 1, x: 2}"):
            self.assertTrue(any("duplicate key" in e for e in check.inspect_text(
                "---\n" + fm + "\n---\n")))
        self.assertEqual([], check.inspect_text(
            "---\ndefaults: &d {description: inherited}\n<<: *d\nname: example\n---\n"))

    def test_discovery_includes_hidden_nested_and_plugin_skills(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for name in ("skills/a/SKILL.md", "plugins/p/skills/b/SKILL.md",
                         "ies/project/.codex/skills/c/SKILL.md"):
                p = root / name; p.parent.mkdir(parents=True); p.write_text(GOOD)
            (root / "skills/a/skill.variant.md").write_text("<<<<<<< HEAD")
            (root / "skills/a/SKILL.md.backup").write_text("<<<<<<< HEAD")
            (root / "skills/app/SKILL.md").mkdir(parents=True)
            self.assertEqual(3, len(check.discover([root, root / "skills"])))
            with self.assertRaises(ValueError):
                check.discover([root / "absent"])
            with self.assertRaises(ValueError):
                check.discover([root / "skills/app"])

    def test_baseline_allows_only_unchanged_debt(self):
        bad = {"skills/a/SKILL.md": {"sha256": "old", "errors": ["bad YAML"]}}
        baseline = {"skills/a/SKILL.md": {"sha256": "old", "reason": "Review pending"}}
        self.assertEqual(({}, ["skills/a/SKILL.md"]), check.apply_baseline(bad, baseline))
        changed = {"skills/a/SKILL.md": {"sha256": "new", "errors": ["bad YAML"]}}
        self.assertTrue(check.apply_baseline(changed, baseline)[0])
        self.assertTrue(check.apply_baseline({}, baseline)[0])
        self.assertTrue(check.apply_baseline(bad, {})[0])
        self.assertTrue(check.apply_baseline(bad, {"skills/a/SKILL.md": {
            "sha256": "old", "reason": ""}})[0])

    def test_cli_status_and_unreadable_text(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "SKILL.md"; p.write_text(GOOD)
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(0, check.main([str(p)]))
                p.write_bytes(b"\xff")
                self.assertEqual(1, check.main([str(p)]))
                self.assertEqual(2, check.main([str(p.parent / "absent")]))
                baseline = p.parent / "debt.json"; baseline.write_text("[]")
                self.assertEqual(2, check.main([str(p), "--baseline", str(baseline)]))

    def test_real_regression_old_scalar_corruption(self):
        # Minimal reproducer: YAML can parse while the skill remains corrupted.
        text = ("---\nname: gf3-trit-oracle <<<<<<< HEAD\n"
                "description: 'Classify trits >>>>>>> origin/main'\n"
                "deployed: 2026-02-19 =======\n---\n")
        self.assertTrue(check.inspect_text(text))

    def test_corrected_skill_files(self):
        for name in ("did-passport-interleave", "gf3-trit-oracle", "benchmark"):
            with self.subTest(name=name):
                self.assertEqual([], check.inspect_text(
                    (ROOT / "skills" / name / "SKILL.md").read_text()))

    def test_documented_trit_arithmetic_exhaustively(self):
        text = (ROOT / "skills/gf3-trit-oracle/SKILL.md").read_text()
        block = next(b for b in re.findall(r"```python\n(.*?)```", text, re.S)
                     if "def gf3_add" in b)
        scope = {}; exec(compile(block, "gf3-trit-oracle arithmetic", "exec"), scope)
        for a in (-1, 0, 1):
            for b in (-1, 0, 1):
                for op, expected in (("gf3_add", a + b), ("gf3_mul", a * b)):
                    value = scope[op](a, b)
                    self.assertIn(value, (-1, 0, 1))
                    self.assertEqual(expected % 3, value % 3)
                c = scope["build_triad"](a, b)
                self.assertIn(c, (-1, 0, 1))
                self.assertTrue(scope["is_valid_triad"](a, b, c))
                self.assertEqual(1, sum(scope["is_valid_triad"](a, b, z) for z in (-1, 0, 1)))

    def test_benchmark_shell_examples_parse(self):
        text = (ROOT / "skills/benchmark/SKILL.md").read_text()
        for block in re.findall(r"```bash\n(.*?)```", text, re.S):
            result = subprocess.run(["bash", "-n"], input=block, text=True, capture_output=True)
            self.assertEqual(0, result.returncode, result.stderr)


if __name__ == "__main__":
    unittest.main()
