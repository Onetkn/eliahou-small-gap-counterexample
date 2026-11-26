"""Build the project and check the transitive axioms of its audited declarations."""

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys


ROOT = Path(__file__).resolve().parent
MAIN_THEOREM = "Eliahou.Counterexample.not_smallGapConjecture"
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
REPORT_PATTERN = re.compile(
    r"^'(?P<name>[^'\r\n]+)' "
    r"(?:depends on axioms:\s*\[(?P<axioms>[^\]]*)\]"
    r"|(?P<none>does not depend on any axioms))[ \t]*$",
    re.MULTILINE,
)


def select_lake():
    """Prefer the isolated Windows installation, otherwise use lake on PATH."""
    env = os.environ.copy()
    local_elan = ROOT / ".tools" / "elan"
    local_lake = local_elan / "bin" / "lake.exe"
    if os.name == "nt" and local_lake.is_file():
        env["ELAN_HOME"] = str(local_elan)
        return str(local_lake), env
    lake = shutil.which("lake")
    if lake is None:
        raise RuntimeError("lake was not found. Install elan and the pinned lean-toolchain first.")
    return lake, env


def run_stage(command, env, stages, capture=False):
    print("\n> " + " ".join(str(part) for part in command), flush=True)
    lines = []
    with subprocess.Popen(
        command, cwd=ROOT, env=env, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, text=True, encoding="utf-8", errors="replace",
    ) as process:
        try:
            for line in process.stdout:
                print(line, end="", flush=True)
                if capture:
                    lines.append(line)
            code = process.wait()
        except BaseException:
            process.terminate()
            process.wait()
            raise
    stages.append({"command": [Path(command[0]).name, *command[1:]], "exit_code": code})
    if code:
        raise RuntimeError(f"Command failed with exit code {code}: {' '.join(command)}")
    return "".join(lines)


def expected_declarations():
    source = (ROOT / "Audit.lean").read_text(encoding="utf-8")
    names = re.findall(r"^\s*#print\s+axioms\s+([A-Za-z0-9_.]+)\s*$", source, re.MULTILINE)
    if MAIN_THEOREM not in names:
        raise RuntimeError(f"Audit.lean must request #print axioms {MAIN_THEOREM}.")
    if len(names) != len(set(names)):
        raise RuntimeError("Audit.lean contains duplicate axiom requests.")
    return names


def parse_axioms(output, expected):
    output = output.replace("\r\n", "\n")
    matches = list(REPORT_PATTERN.finditer(output))
    declarations = {}
    errors = []
    for match in matches:
        name = match.group("name")
        if name in declarations:
            errors.append(f"Duplicate axiom report for {name}.")
        raw = match.group("axioms")
        axioms = [] if raw is None or not raw.strip() else [part.strip() for part in raw.split(",")]
        declarations[name] = axioms
        unexpected = sorted(set(axioms) - ALLOWED_AXIOMS)
        if unexpected:
            errors.append(f"Unexpected axioms for {name}: {', '.join(unexpected)}.")
    # Reject unparsed report lines rather than silently skipping an output change.
    for line in re.finditer(r"^.*(?:depends on axioms:|does not depend on any axioms).*$", output, re.MULTILINE):
        if not any(match.start() <= line.start() < match.end() for match in matches):
            errors.append(f"Unrecognized axiom report: {line.group(0)}")
    missing = sorted(set(expected) - declarations.keys())
    if missing:
        errors.append("Missing axiom reports: " + ", ".join(missing) + ".")
    if MAIN_THEOREM not in declarations:
        errors.append(f"The main theorem {MAIN_THEOREM} was not audited.")
    return declarations, errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, metavar="PATH", help="also save a machine-readable verification report")
    args = parser.parse_args()
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="replace")
    report = {
        "status": "failed",
        "toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "required_main_theorem": MAIN_THEOREM,
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "stages": [],
        "declarations": {},
        "errors": [],
    }
    try:
        expected = expected_declarations()
        report["expected_declarations"] = expected
        lake, env = select_lake()
        run_stage([lake, "build"], env, report["stages"])
        output = run_stage([lake, "env", "lean", "Audit.lean"], env, report["stages"], capture=True)
        report["declarations"], report["errors"] = parse_axioms(output, expected)
        if not report["errors"]:
            report["status"] = "passed"
    except (OSError, RuntimeError) as exc:
        report["errors"].append(str(exc))
    except KeyboardInterrupt:
        report["errors"].append("Verification interrupted.")
    if args.json:
        try:
            args.json.parent.mkdir(parents=True, exist_ok=True)
            args.json.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
            print(f"\nJSON report: {args.json.resolve()}")
        except OSError as exc:
            report["status"] = "failed"
            report["errors"].append(f"Could not write JSON report: {exc}")
    if report["status"] == "passed":
        print(f"\nPASS: build and axiom audit for {len(report['declarations'])} declarations, including {MAIN_THEOREM}.")
        return 0
    for error in report["errors"]:
        print(f"FAIL: {error}", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
