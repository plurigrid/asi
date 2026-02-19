from __future__ import annotations

import json
import shutil
import subprocess
import sys
from pathlib import Path


SCRIPT_PATH = Path(__file__).resolve().parents[1] / "scripts" / "enforce_skill_invariants.py"


def _write_skill(skills_dir: Path, name: str, body: str = "") -> None:
    path = skills_dir / name
    path.mkdir(parents=True, exist_ok=True)
    (path / "SKILL.md").write_text(
        f"---\nname: {name}\ndescription: test skill {name}\n---\n\n{body}\n",
        encoding="utf-8",
    )


def _write_config(
    path: Path,
    max_seconds_between_snapshots: int | None = None,
    strict_cost_decrease_on_skill_growth: bool = True,
) -> None:
    policy = {"strict_cost_decrease_on_skill_growth": strict_cost_decrease_on_skill_growth}
    if max_seconds_between_snapshots is not None:
        policy["max_seconds_between_snapshots"] = max_seconds_between_snapshots
    payload = {
        "version": 1,
        "hubs": ["hub-skill"],
        "seed_edges": {"hub-skill": ["core-skill"]},
        "pattern_edges": {},
        "policy": policy,
    }
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _run_checker(
    skills_dir: Path,
    config_path: Path,
    state_path: Path,
    update_state: bool = False,
    oversight: bool = False,
    oversight_note: str | None = None,
    include_untracked: bool = False,
    emit_intent: Path | None = None,
) -> subprocess.CompletedProcess[str]:
    cmd = [
        sys.executable,
        str(SCRIPT_PATH),
        "--skills-dir",
        str(skills_dir),
        "--config",
        str(config_path),
        "--state",
        str(state_path),
    ]
    if update_state:
        cmd.append("--update-state")
    if oversight:
        cmd.append("--human-oversight")
    if oversight_note:
        cmd.extend(["--oversight-note", oversight_note])
    if include_untracked:
        cmd.append("--include-untracked")
    if emit_intent is not None:
        cmd.extend(["--emit-intent", str(emit_intent)])
    return subprocess.run(cmd, capture_output=True, text=True, check=False)


def test_bootstrap_writes_state(tmp_path: Path) -> None:
    skills_dir = tmp_path / "skills"
    skills_dir.mkdir()
    config_path = tmp_path / "config.json"
    state_path = tmp_path / "state.json"
    _write_config(config_path)

    _write_skill(skills_dir, "hub-skill", body="`core-skill`")
    _write_skill(skills_dir, "core-skill")

    result = _run_checker(
        skills_dir=skills_dir,
        config_path=config_path,
        state_path=state_path,
        update_state=True,
    )

    assert result.returncode == 0, result.stdout + result.stderr
    assert state_path.exists()


def test_skill_count_decrease_fails_without_oversight(tmp_path: Path) -> None:
    skills_dir = tmp_path / "skills"
    skills_dir.mkdir()
    config_path = tmp_path / "config.json"
    state_path = tmp_path / "state.json"
    _write_config(config_path)

    _write_skill(skills_dir, "hub-skill", body="`core-skill`")
    _write_skill(skills_dir, "core-skill")

    baseline = _run_checker(
        skills_dir=skills_dir,
        config_path=config_path,
        state_path=state_path,
        update_state=True,
    )
    assert baseline.returncode == 0, baseline.stdout + baseline.stderr

    shutil.rmtree(skills_dir / "core-skill")

    result = _run_checker(
        skills_dir=skills_dir,
        config_path=config_path,
        state_path=state_path,
    )

    assert result.returncode != 0
    assert "Skill count decreased" in result.stdout


def test_skill_count_decrease_can_be_waived_with_oversight(tmp_path: Path) -> None:
    skills_dir = tmp_path / "skills"
    skills_dir.mkdir()
    config_path = tmp_path / "config.json"
    state_path = tmp_path / "state.json"
    _write_config(config_path)

    _write_skill(skills_dir, "hub-skill", body="`core-skill`")
    _write_skill(skills_dir, "core-skill")

    baseline = _run_checker(
        skills_dir=skills_dir,
        config_path=config_path,
        state_path=state_path,
        update_state=True,
    )
    assert baseline.returncode == 0, baseline.stdout + baseline.stderr

    shutil.rmtree(skills_dir / "core-skill")

    waived = _run_checker(
        skills_dir=skills_dir,
        config_path=config_path,
        state_path=state_path,
        oversight=True,
        oversight_note="manual consolidation approved",
    )
    assert waived.returncode == 0, waived.stdout + waived.stderr


def test_skill_growth_requires_reachability_cost_drop(tmp_path: Path) -> None:
    skills_dir = tmp_path / "skills"
    skills_dir.mkdir()
    config_path = tmp_path / "config.json"
    state_path = tmp_path / "state.json"
    _write_config(config_path)

    _write_skill(skills_dir, "hub-skill", body="`core-skill`")
    _write_skill(skills_dir, "core-skill")

    baseline = _run_checker(
        skills_dir=skills_dir,
        config_path=config_path,
        state_path=state_path,
        update_state=True,
    )
    assert baseline.returncode == 0, baseline.stdout + baseline.stderr

    # Add a new isolated skill: skill count grows but coverage worsens.
    _write_skill(skills_dir, "isolated-skill")

    result = _run_checker(
        skills_dir=skills_dir,
        config_path=config_path,
        state_path=state_path,
    )
    assert result.returncode != 0
    assert "did not strictly decrease" in result.stdout


def test_untracked_skills_ignored_by_default_in_git_repo(tmp_path: Path) -> None:
    repo = tmp_path
    skills_dir = repo / "skills"
    skills_dir.mkdir()
    config_path = repo / "config.json"
    state_path = repo / "state.json"
    _write_config(config_path)

    _write_skill(skills_dir, "hub-skill", body="`core-skill`")
    _write_skill(skills_dir, "core-skill")

    subprocess.run(["git", "init"], cwd=repo, check=True, capture_output=True, text=True)
    subprocess.run(
        ["git", "add", "skills/hub-skill/SKILL.md", "skills/core-skill/SKILL.md"],
        cwd=repo,
        check=True,
        capture_output=True,
        text=True,
    )

    baseline = _run_checker(
        skills_dir=skills_dir,
        config_path=config_path,
        state_path=state_path,
        update_state=True,
    )
    assert baseline.returncode == 0, baseline.stdout + baseline.stderr

    # Add local untracked skill; default mode should ignore it.
    _write_skill(skills_dir, "local-untracked-skill")

    default_mode = _run_checker(
        skills_dir=skills_dir,
        config_path=config_path,
        state_path=state_path,
    )
    assert default_mode.returncode == 0, default_mode.stdout + default_mode.stderr

    explicit_untracked = _run_checker(
        skills_dir=skills_dir,
        config_path=config_path,
        state_path=state_path,
        include_untracked=True,
    )
    assert explicit_untracked.returncode != 0


def test_time_density_violation(tmp_path: Path) -> None:
    skills_dir = tmp_path / "skills"
    skills_dir.mkdir()
    config_path = tmp_path / "config.json"
    state_path = tmp_path / "state.json"
    _write_config(
        config_path,
        max_seconds_between_snapshots=1,
        strict_cost_decrease_on_skill_growth=False,
    )

    _write_skill(skills_dir, "hub-skill", body="`core-skill`")
    _write_skill(skills_dir, "core-skill")

    baseline = _run_checker(
        skills_dir=skills_dir,
        config_path=config_path,
        state_path=state_path,
        update_state=True,
    )
    assert baseline.returncode == 0, baseline.stdout + baseline.stderr

    payload = json.loads(state_path.read_text(encoding="utf-8"))
    payload["generated_at"] = "2000-01-01T00:00:00+00:00"
    state_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    _write_skill(skills_dir, "new-skill")
    _write_skill(skills_dir, "hub-skill", body="`core-skill` `new-skill`")

    result = _run_checker(
        skills_dir=skills_dir,
        config_path=config_path,
        state_path=state_path,
    )
    assert result.returncode != 0
    assert "Time density violation" in result.stdout


def test_time_density_not_enforced_when_metrics_unchanged(tmp_path: Path) -> None:
    skills_dir = tmp_path / "skills"
    skills_dir.mkdir()
    config_path = tmp_path / "config.json"
    state_path = tmp_path / "state.json"
    _write_config(config_path, max_seconds_between_snapshots=1)

    _write_skill(skills_dir, "hub-skill", body="`core-skill`")
    _write_skill(skills_dir, "core-skill")

    baseline = _run_checker(
        skills_dir=skills_dir,
        config_path=config_path,
        state_path=state_path,
        update_state=True,
    )
    assert baseline.returncode == 0, baseline.stdout + baseline.stderr

    payload = json.loads(state_path.read_text(encoding="utf-8"))
    payload["generated_at"] = "2000-01-01T00:00:00+00:00"
    state_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    result = _run_checker(
        skills_dir=skills_dir,
        config_path=config_path,
        state_path=state_path,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_emit_intent_writes_payload_with_witness(tmp_path: Path) -> None:
    skills_dir = tmp_path / "skills"
    skills_dir.mkdir()
    config_path = tmp_path / "config.json"
    state_path = tmp_path / "state.json"
    intent_path = tmp_path / "intent.json"
    _write_config(config_path)

    _write_skill(skills_dir, "hub-skill", body="`core-skill`")
    _write_skill(skills_dir, "core-skill")

    baseline = _run_checker(
        skills_dir=skills_dir,
        config_path=config_path,
        state_path=state_path,
        update_state=True,
    )
    assert baseline.returncode == 0, baseline.stdout + baseline.stderr

    result = _run_checker(
        skills_dir=skills_dir,
        config_path=config_path,
        state_path=state_path,
        emit_intent=intent_path,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert intent_path.exists()

    payload = json.loads(intent_path.read_text(encoding="utf-8"))
    assert payload["type"] == "ReachabilityInvariantIntent"
    assert isinstance(payload["witness"], str) and payload["witness"]
    assert payload["valid"] is True
    assert payload["constraints"]["non_decreasing_skill_count_unless_oversight"] is True
    assert payload["constraints"]["steadily_decreasing_reachability_cost_unless_oversight"] is True
    assert payload["constraints"]["locally_dense_time_unless_oversight"] is True
    assert payload["timing"]["metrics_changed"] is False


def test_emit_intent_captures_time_density_violation(tmp_path: Path) -> None:
    skills_dir = tmp_path / "skills"
    skills_dir.mkdir()
    config_path = tmp_path / "config.json"
    state_path = tmp_path / "state.json"
    intent_path = tmp_path / "intent.json"
    _write_config(
        config_path,
        max_seconds_between_snapshots=1,
        strict_cost_decrease_on_skill_growth=False,
    )

    _write_skill(skills_dir, "hub-skill", body="`core-skill`")
    _write_skill(skills_dir, "core-skill")

    baseline = _run_checker(
        skills_dir=skills_dir,
        config_path=config_path,
        state_path=state_path,
        update_state=True,
    )
    assert baseline.returncode == 0, baseline.stdout + baseline.stderr

    payload = json.loads(state_path.read_text(encoding="utf-8"))
    payload["generated_at"] = "2000-01-01T00:00:00+00:00"
    state_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    _write_skill(skills_dir, "new-skill")
    _write_skill(skills_dir, "hub-skill", body="`core-skill` `new-skill`")

    result = _run_checker(
        skills_dir=skills_dir,
        config_path=config_path,
        state_path=state_path,
        emit_intent=intent_path,
    )
    assert result.returncode != 0
    assert intent_path.exists()

    intent = json.loads(intent_path.read_text(encoding="utf-8"))
    assert intent["valid"] is False
    assert intent["timing"]["metrics_changed"] is True
    assert intent["constraints"]["locally_dense_time_unless_oversight"] is False
