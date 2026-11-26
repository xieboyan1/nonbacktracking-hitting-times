"""Replay all local proofs using Lean 4.19.0 and the mathlib environment."""
from hashlib import sha256
import os
from pathlib import Path
import re
import subprocess
import tempfile


MODULES = (
    "Witness", "Stationary", "Hitting", "Walks", "Branch", "Theta",
    "Fundamental", "Gap", "GapData", "Corridors", "Bounds", "Kemeny",
    "Strict", "Forward", "Nonbacktracking",
)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def main():
    source = Path(__file__).resolve().parent
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    if "version 4.19.0," not in version:
        raise RuntimeError("The package is pinned to Lean 4.19.0. Found " + version)
    print(version, flush=True)
    print("mathlib v4.19.0 | warnings treated as errors", flush=True)
    with tempfile.TemporaryDirectory() as build:
        env = os.environ.copy()
        paths = [build, env.get("LEAN_PATH", "")]
        env["LEAN_PATH"] = os.pathsep.join(filter(None, paths))
        for module in MODULES:
            src = source / (module + ".lean")
            print(f"\n{src.name}  sha256={sha256(src.read_bytes()).hexdigest()}", flush=True)
            result = subprocess.run(
                ["lean", "-DwarningAsError=true", "-o", str(Path(build) / (module + ".olean")), src.name],
                cwd=source, env=env, text=True, encoding="utf-8", errors="replace",
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            )
            print(result.stdout.rstrip(), flush=True)
            result.check_returncode()
            reports = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", result.stdout, re.S)
            for report in reports:
                unexpected = {x.strip() for x in report.split(",")} - ALLOWED_AXIOMS
                if unexpected:
                    raise RuntimeError(f"Unexpected axioms in {module}: {unexpected}")
            if module == "Nonbacktracking" and len(reports) != 12:
                raise RuntimeError("Missing final theorem reports.")
    print("\nAll 15 source modules checked. All 12 final axiom reports passed.", flush=True)


if __name__ == "__main__":
    main()
