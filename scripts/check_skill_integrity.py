#!/usr/bin/env python3
"""Check live SKILL.md files without repairing them. Requires only PyYAML.

By default scan every canonical SKILL.md, including plugin and nested agent
trees (hidden directories included). Fenced code is scanned
because unresolved merges there still change agent instructions. No blanket
exceptions for examples: store literal fixtures as .txt files or test strings,
not canonical SKILL.md entrypoints.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

import yaml

DEFAULT_ROOTS = (".",)
MARKER = re.compile(r"(?<!<)<{7,}(?=\s|$)|(?<!>)>{7,}(?=\s|$)|"
                    r"(?<!\|)\|{7,}(?=\s|$)|^\s*={7}\s*$")


class UniqueSafeLoader(yaml.SafeLoader):
    """Reject duplicate mapping keys rather than silently taking the last value."""


def unique_mapping(loader, node, deep=False):
    seen = set()
    for key_node, _ in node.value:
        if key_node.tag == "tag:yaml.org,2002:merge":
            continue
        key = loader.construct_object(key_node, deep=deep)
        try:
            if key in seen:
                raise yaml.constructor.ConstructorError(
                    None, None, f"duplicate key: {key}", key_node.start_mark)
            seen.add(key)
        except TypeError as exc:
            raise yaml.constructor.ConstructorError(
                None, None, "unhashable mapping key", key_node.start_mark) from exc
    return yaml.SafeLoader.construct_mapping(loader, node, deep=deep)


UniqueSafeLoader.add_constructor(
    yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, unique_mapping)


def inspect_text(text):
    """Return independently collected marker and frontmatter diagnostics."""
    lines = text.splitlines()
    errors = [f"line {i}: unresolved merge marker" for i, line in enumerate(lines, 1)
              if MARKER.search(line)]
    if not lines or lines[0] != "---":
        return errors + ["line 1: missing YAML front matter opening delimiter"]
    try:
        end = lines.index("---", 1)
    except ValueError:
        return errors + ["line 1: missing YAML front matter closing delimiter"]
    # A previous frontmatter repair folded separator tokens into scalar values.
    errors.extend(f"line {i + 1}: unresolved merge marker" for i in range(1, end)
                  if re.search(r"(?<!=)={7}(?!=)", lines[i])
                  and not MARKER.search(lines[i]))
    try:
        data = yaml.load("\n".join(lines[1:end]), Loader=UniqueSafeLoader)
        if not isinstance(data, dict):
            errors.append("front matter must be a YAML mapping")
        else:
            for key in ("name", "description"):
                if not isinstance(data.get(key), str) or not data[key].strip():
                    errors.append(f"front matter {key} must be a nonempty string")
    except yaml.YAMLError as exc:
        mark = getattr(exc, "problem_mark", None)
        location = f"line {mark.line + 2}: " if mark else ""
        errors.append(location + "invalid YAML: " +
                      (getattr(exc, "problem", None) or str(exc).splitlines()[0]))
    return errors


def discover(roots):
    files = set()
    for root in roots:
        path = Path(root)
        if not path.exists():
            raise ValueError(f"no such path: {path}")
        if path.is_file():
            if path.name != "SKILL.md":
                raise ValueError(f"expected SKILL.md: {path}")
            files.add(path)
        else:
            files.update(p for p in path.rglob("SKILL.md") if p.is_file())
    if not files:
        raise ValueError("no SKILL.md files found")
    return sorted(files)


def scan(files):
    results = {}
    for path in files:
        raw = path.read_bytes()
        try:
            errors = inspect_text(raw.decode("utf-8"))
        except UnicodeDecodeError:
            errors = ["invalid UTF-8"]
        if errors:
            results[path.as_posix()] = {
                "sha256": hashlib.sha256(raw).hexdigest(), "errors": errors}
    return results


def apply_baseline(results, baseline):
    """Exempt only identical known debt; fail stale, changed, or new entries."""
    failures = {}
    deferred = []
    for path, result in results.items():
        entry = baseline.get(path, {})
        if (entry.get("sha256") == result["sha256"]
                and isinstance(entry.get("reason"), str) and entry["reason"].strip()):
            deferred.append(path)
        else:
            failures[path] = result["errors"]
    for path in baseline.keys() - results.keys():
        failures[path] = ["stale baseline entry: remove after repair/deletion; "
                          "baseline must match the scan scope"]
    return failures, deferred


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*", help="roots or individual SKILL.md files")
    parser.add_argument("--baseline", type=Path, help="explicit content-hashed known debt")
    parser.add_argument("--json", action="store_true", help="emit machine-readable audit")
    args = parser.parse_args(argv)
    try:
        files = discover(args.paths or DEFAULT_ROOTS)
        results = scan(files)
        baseline = json.loads(args.baseline.read_text()) if args.baseline else {}
        if not isinstance(baseline, dict) or any(not isinstance(v, dict) for v in baseline.values()):
            raise ValueError("baseline must map paths to sha256/reason objects")
        failures, deferred = apply_baseline(results, baseline)
    except (OSError, ValueError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2
    report = {"checked": len(files), "affected": len(results),
              "marker_files": sum(any("merge marker" in e for e in r["errors"])
                                  for r in results.values()),
              "frontmatter_files": sum(any("merge marker" not in e for e in r["errors"])
                                       for r in results.values()),
              "failures": failures, "deferred": deferred, "findings": results}
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        for path, errors in sorted(failures.items()):
            for error in errors:
                print(f"ERROR {path}: {error}")
        for path in deferred:
            print(f"DEFERRED {path}")
        print(f"Checked {len(files)} SKILL.md: {report['marker_files']} marker files, "
              f"{report['frontmatter_files']} front matter failures; "
              f"{len(failures)} blocking, {len(deferred)} unchanged deferred")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
