"""Check the release inputs, extract nine-point sources, or rebuild a theorem."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory
from zipfile import ZipFile

HERE = Path(__file__).resolve().parent
CASES = ("chalk_ge10", "n6", "n7", "n8", "n9")
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def verify(root, plan):
    rows = plan["files"] + plan.get("certificate_data", [])
    for row in rows:
        path = root / row["path"]
        require(path.stat().st_size == row["bytes"] and digest(path) == row["sha256"],
                f"Source mismatch: {row['path']}")
    order = {name: index for index, name in enumerate(plan["build_order"])}
    source_names = {row["path"][:-5].replace("/", ".") for row in plan["files"]}
    require(source_names == order.keys() and len(order) == len(plan["build_order"]),
            "Build order does not cover the exact source manifest")
    print(f"{plan['project']}: {len(rows)} input files verified", flush=True)


def extract(root, plan, directory):
    rows = {row["path"]: row for row in plan["files"]}
    parts = plan["assets"]
    names = [name for part in parts for name in part["members"]]
    require(set(names) == rows.keys() and len(names) == len(rows), "Invalid asset partition")
    require(not any((root / name).exists() for name in names),
            "Use a source tree without previously extracted nine-point files")
    with TemporaryDirectory(prefix="extract-", dir=root) as scratch:
        scratch = Path(scratch)
        for part in parts:
            asset = directory / part["file"]
            require(asset.stat().st_size == part["bytes"] and digest(asset) == part["sha256"],
                    f"Asset mismatch: {asset}")
            with ZipFile(asset) as archive:
                require(archive.namelist() == part["members"], f"Unexpected ZIP entries: {asset}")
                for name in part["members"]:
                    target = scratch / name
                    require(target.resolve().is_relative_to(scratch.resolve()), "Unsafe asset path")
                    target.parent.mkdir(parents=True, exist_ok=True)
                    with archive.open(name) as stream, target.open("xb") as output:
                        shutil.copyfileobj(stream, output)
        verify(scratch, plan)
        for folder in scratch.iterdir():
            require(not (root / folder.name).exists(), f"Destination already exists: {folder.name}")
        for folder in scratch.iterdir():
            folder.rename(root / folder.name)


def build(root, plan, memory, dependencies):
    verify(root, plan)
    env = os.environ.copy()
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"):
        env.pop(key, None)
    version = subprocess.check_output(["lean", "--version"], cwd=root, env=env, text=True)
    require("version 4.30.0," in version, f"Unexpected Lean version: {version.strip()}")
    library_paths = []
    for pkg in read(root / "lake-manifest.json")["packages"]:
        location = dependencies / pkg["name"]
        cmd = ["git", "-C", str(location)]
        head = subprocess.check_output([*cmd, "rev-parse", "HEAD"], text=True).strip()
        dirty = subprocess.check_output([*cmd, "status", "--porcelain", "--untracked-files=no"], text=True)
        require(head == pkg["rev"] and not dirty, f"Dependency mismatch: {pkg['name']}")
        library = location / ".lake" / "build" / "lib" / "lean"
        if library.is_dir():
            library_paths.append(library)
        elif pkg["name"] == "mathlib":
            raise ValueError(f"Mathlib cache missing: {library}")

    with TemporaryDirectory(prefix="mordell-lean-") as scratch:
        out = Path(scratch)
        env["LEAN_PATH"] = os.pathsep.join(map(str, [out, *library_paths]))
        cmd = ["lean", "-j1", f"-M{memory}", "-DautoImplicit=false", "-R", str(root)]
        for i, module in enumerate(plan["build_order"], 1):
            stem = module.replace(".", "/")
            source = root / f"{stem}.lean"
            output = out / f"{stem}.olean"
            output.parent.mkdir(parents=True, exist_ok=True)
            print(f"[{i}/{len(plan['build_order'])}] {module}", flush=True)
            subprocess.run([*cmd, "-o", str(output), str(source)], cwd=root, env=env, check=True)
        audit = subprocess.check_output([*cmd, "Audit.lean"], cwd=root, env=env, text=True, encoding="utf-8")
        print(audit, end="")
        for theorem in plan["theorems"]:
            prefix = re.escape(f"'{theorem}' depends on axioms:")
            match = re.search(prefix + r"\s*\[([^]]*)\]", audit)
            require(match is not None, f"Missing axiom audit for {theorem}")
            used = {name.strip() for name in match[1].split(",")} - {""}
            require(used <= AXIOMS, f"Unexpected axioms for {theorem}: {used - AXIOMS}")
    print("All project sources rebuilt and final theorem axioms audited.")


def main():
    # Lean prints mathematical symbols that legacy Windows encodings cannot represent.
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("verify", "extract", "build"))
    parser.add_argument("case", choices=CASES)
    parser.add_argument("--assets", type=Path)
    parser.add_argument("--dependency-cache", type=Path)
    parser.add_argument("--memory", type=int, default=8192)
    args = parser.parse_args()
    root = HERE / args.case
    plan = read(root / "SOURCE_MANIFEST.json")
    if args.action == "extract":
        if args.case != "n9" or args.assets is None:
            parser.error("extract requires n9 and --assets DIRECTORY")
        extract(root, plan, args.assets.resolve())
    elif args.action == "build":
        if args.memory < 1024:
            parser.error("--memory must be at least 1024 MiB")
        dependencies = args.dependency_cache or root / ".lake" / "packages"
        build(root, plan, args.memory, dependencies.resolve())
    else:
        verify(root, plan)


if __name__ == "__main__":
    main()
