"""Run the official targeted cache in the pristine Mathlib snapshot.

Invoke using `lake env python cache_mathlib.py MODULE...` from lean/.
This preserves Mathlib's upstream manifest hash despite path-based installation.
"""
from pathlib import Path
import shutil
import subprocess
import sys

root = Path(__file__).resolve().parent
sources = root / "Bootstrap" / "sources"
mathlib = sources / "mathlib"
modules = sys.argv[1:] or [
    "Mathlib.Data.Finset.Card",
    "Mathlib.Order.Interval.Finset.Nat", "Mathlib.Data.Set.Basic",
    "Mathlib.Tactic.Linarith", "Mathlib.Tactic.FinCases",
    "Mathlib.Data.Fin.Tuple.Basic", "Mathlib.Algebra.BigOperators.Group.Finset.Basic",
]
executable = mathlib / ".lake" / "build" / "bin" / ("cache.exe" if sys.platform == "win32" else "cache")
status = subprocess.call([str(executable), "get", "--repo=leanprover-community/mathlib4", *modules], cwd=mathlib)
# Official archives contain dependency paths relative to the Mathlib root.
# Mirror those build artifacts to this project's actual snapshot package paths.
dependency_outputs = mathlib / ".lake" / "packages"
if dependency_outputs.exists():
    for package in dependency_outputs.iterdir():
        source = package / ".lake" / "build"
        destination = sources / package.name / ".lake" / "build"
        if source.is_dir() and (sources / package.name).is_dir():
            shutil.copytree(source, destination, dirs_exist_ok=True)
raise SystemExit(status)
