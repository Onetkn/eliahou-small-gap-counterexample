"""Fetch pinned official source snapshots using the authenticated GitHub CLI.

No credential material is read or stored by this script. Sources are staged
under Bootstrap/sources; Lake configuration is not changed by downloading.
"""
import base64
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parent
STAGE = ROOT / "Bootstrap" / "sources"
MATHLIB_REV = "fc4f59e577feb1a4956671bc04ac18aaaf8cd842"


def api(endpoint):
    return json.loads(subprocess.check_output(["gh", "api", endpoint], timeout=60))


def fetch(item):
    name, repo, rev = item["name"], item["repo"], item["rev"]
    archive = STAGE / f"{name}-{rev}.tar.gz"
    target = STAGE / name
    if not archive.exists() or archive.stat().st_size == 0:
        with archive.open("wb") as out:
            subprocess.run(["gh", "api", f"repos/{repo}/tarball/{rev}"],
                           stdout=out, check=True, timeout=240)
    digest = hashlib.file_digest(archive.open("rb"), "sha256").hexdigest()
    if not target.exists():
        target.mkdir(parents=True)
        with tarfile.open(archive, "r:gz") as tf:
            for member in tf:
                parts = Path(member.name).parts
                if len(parts) <= 1:
                    continue
                member.name = str(Path(*parts[1:]))
                tf.extract(member, target, filter="data")
    print(f"Fetched {name} {rev}: {archive.stat().st_size} bytes", flush=True)
    return dict(item, archive_sha256=digest)


def main():
    STAGE.mkdir(parents=True, exist_ok=True)
    manifest_file = api(
        f"repos/leanprover-community/mathlib4/contents/lake-manifest.json?ref={MATHLIB_REV}")
    manifest = json.loads(base64.b64decode(manifest_file["content"]))
    packages = [dict(name="mathlib", repo="leanprover-community/mathlib4", rev=MATHLIB_REV)]
    packages.extend(dict(name=p["name"], repo=p["url"].removeprefix("https://github.com/"), rev=p["rev"])
                    for p in manifest["packages"])
    with ThreadPoolExecutor(max_workers=3) as pool:
        fetched = list(pool.map(fetch, packages))
    (STAGE / "source-lock.json").write_text(json.dumps(fetched, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
