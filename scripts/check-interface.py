#!/usr/bin/env python3
"""Compare elaborated types locally and audit every advertised proof's axioms."""
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
AXIOM_REPORT = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", re.M)
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def main():
    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    challenge = config["challenge_module"]
    solution = config["solution_module"]
    theorems = config["theorem_names"]
    allowed = set(config["permitted_axioms"])
    if not theorems or len(theorems) != len(set(theorems)):
        raise SystemExit("Expected a nonempty list of distinct advertised theorems")
    if allowed != STANDARD_AXIOMS:
        raise SystemExit("Comparator permitted_axioms differs from the standard axiom set")

    subprocess.run(
        ["lake", "env", "lean", "--run", "scripts/check-statements.lean",
         challenge, solution, *theorems],
        cwd=ROOT, check=True,
    )

    with tempfile.TemporaryDirectory(prefix="principia-axioms-") as directory:
        audit = Path(directory) / "Audit.lean"
        commands = "\n".join(f"#print axioms {name}" for name in theorems)
        audit.write_text(f"module\n\nimport {solution}\n\n{commands}\n", encoding="utf-8")
        result = subprocess.run(
            ["lake", "env", "lean", str(audit)], cwd=ROOT, check=True,
            stdout=subprocess.PIPE, text=True,
        )

    print(result.stdout, end="")
    reports = {
        name: {axiom.strip() for axiom in axioms.split(",") if axiom.strip()}
        for name, axioms in AXIOM_REPORT.findall(result.stdout)
    }
    axiom_free = re.findall(r"^'([^']+)' does not depend on any axioms$", result.stdout, re.M)
    reports.update((name, set()) for name in axiom_free)
    if reports.keys() != set(theorems):
        raise SystemExit("Expected one axiom report for each advertised theorem")
    for name, axioms in reports.items():
        unexpected = axioms - allowed
        if unexpected:
            raise SystemExit(f"{name} uses unexpected axioms: {', '.join(sorted(unexpected))}")
    print(f"Axiom audit passed for {len(theorems)} declarations")


if __name__ == "__main__":
    main()
