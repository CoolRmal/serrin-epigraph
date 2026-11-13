#!/usr/bin/env python3
"""Audit the three Solution targets' actual transitive axiom dependencies.

This development check is separate from sandboxed Comparator verification.
Intentional holes in the independent Challenge are not imported or audited.
"""

from pathlib import Path
import re
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent.parent
TARGETS = (
    "SerrinEpigraph.verticalDerivative_pos",
    "SerrinEpigraph.rigidity_of_dimension_le_eight",
    "SerrinEpigraph.rigidity_of_oneSidedLinearBound",
)
PERMITTED = {"propext", "Quot.sound", "Classical.choice"}


def main() -> int:
    source = "module\n\nimport Solution\n\n" + "\n".join(
        f"#print axioms {name}" for name in TARGETS
    ) + "\n"
    try:
        with tempfile.TemporaryDirectory(prefix="serrin-axioms-") as directory:
            audit = Path(directory) / "Audit.lean"
            audit.write_text(source, encoding="utf-8")
            result = subprocess.run(
                ["lake", "env", "lean", str(audit)],
                cwd=ROOT,
                capture_output=True,
                text=True,
                timeout=300,
                check=False,
            )
    except (OSError, subprocess.TimeoutExpired) as error:
        print(f"Axiom audit could not finish: {error}", file=sys.stderr)
        return 1

    output = result.stdout + result.stderr
    if result.returncode:
        print(output, end="" if output.endswith("\n") else "\n")
        print("Axiom audit failed: Lean did not elaborate the audit.", file=sys.stderr)
        return 1

    reports: dict[str, list[set[str]]] = {name: [] for name in TARGETS}
    for match in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output):
        name, entries = match.groups()
        if name in reports:
            reports[name].append({entry.strip() for entry in entries.split(",") if entry.strip()})
    for match in re.finditer(r"'([^']+)' does not depend on any axioms", output):
        name = match.group(1)
        if name in reports:
            reports[name].append(set())

    passed = True
    for name in TARGETS:
        if len(reports[name]) != 1:
            print(f"FAIL {name}: expected exactly one axiom report, got {len(reports[name])}")
            passed = False
            continue
        axioms = reports[name][0]
        forbidden = axioms - PERMITTED
        status = "FAIL" if forbidden else "PASS"
        print(f"{status} {name}: {', '.join(sorted(axioms)) or '(no axioms)'}")
        if forbidden:
            print(f"  Forbidden dependencies: {', '.join(sorted(forbidden))}")
            passed = False
    if not passed:
        print("Proof completion has not been established; Comparator remains a separate check.")
        return 1
    print("All target axiom dependencies pass. Run sandboxed Comparator independently.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
