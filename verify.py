#!/usr/bin/env python3
"""Audit frozen evidence or check it in a disposable publication work copy.

An audit authenticates distributed bytes and stored results. It is not a new
execution of the full proof, and the seven-point classification remains cited.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import shutil
import subprocess
import sys
import uuid

ROOT = Path(__file__).resolve().parent
CASES = ("n2-n5", "n6", "n7", "n8", "n9", "n10")
N9_LEAF_REASONS = ("outside", "moment_outside", "quartic_outside", "local", "positive", "cubic_positive", "arb_positive", "discrete_radial_outside", "physical_correction_positive", "quadratic_correction_positive", "arb_correction_positive")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def read_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8-sig"))


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit_files(root: Path = ROOT) -> int:
    manifest = read_json(root / "verification/files.sha256.json")
    for name, expected in manifest["files"].items():
        path = (root / name).resolve()
        require(path.is_relative_to(root.resolve()), f"Unsafe manifest path: {name}")
        require(path.is_file(), f"Missing distributed file: {name}")
        require(digest(path) == expected, f"Checksum mismatch: {name}")
    return len(manifest["files"])


def check_ten(root: Path = ROOT) -> dict:
    """Recompute the witness using integers; require agreement with the certificate."""
    points = [(7, 0), (-7, 0)] + [
        (sx * a, sy * b)
        for a, b in [(21, 9), (8, 20)]
        for sx in [-1, 1]
        for sy in [-1, 1]
    ]
    require(len(set(points)) == 10, "The witness must have ten distinct points.")
    q = sum(x * x + y * y for x, y in points)
    require(q == 4042 and Fraction(5, 2021) * q == 10, "Invalid normalization.")
    require(sum(x for x, y in points) == sum(y for x, y in points) == 0, "Nonzero centroid.")
    distances = [
        (x - u) ** 2 + (y - v) ** 2
        for i, (x, y) in enumerate(points)
        for u, v in points[:i]
    ]
    require(len(distances) == 45 and min(distances) > 0, "Invalid pair distances.")
    product = math.prod(distances)
    ratio = Fraction(product * 9**36, q**45)
    gap = 5 * product * 9**36 - 6 * q**45
    require(gap > 0 and ratio > Fraction(6, 5), "The strict comparison failed.")
    cert = read_json(root / "verification/n10/exact_counterexample_certificate.json")
    checks = {
        "coordinates_w": [list(p) for p in points],
        "q": q,
        "P": str(product),
        "ratio_numerator": str(ratio.numerator),
        "ratio_denominator": str(ratio.denominator),
        "positive_integer_5P9pow36_minus_6qpow45": str(gap),
    }
    for key, value in checks.items():
        require(cert[key] == value, f"Ten-point certificate disagrees: {key}")
    lo, hi = map(Fraction, cert["certified_ratio_interval"])
    require(lo < ratio < hi, "Invalid displayed rational interval.")
    return {"claim": "M10 > C10", "exact_integer_comparison": True}


def audit_case(case: str, root: Path = ROOT) -> dict:
    base = root / "verification" / case
    if case == "n2-n5":
        return {
            "kind": "proofs-and-citations",
            "scope": "Complete elementary proofs for n=2,3; cited global theorems for n=4,5.",
        }
    if case == "n10":
        return check_ten(root)
    if case == "n6":
        result = read_json(base / "global_verification.json")
        require(result["global_upper_bound_certified"] and result["all_equality_cases_classified"], "Incomplete n6 certificate.")
        require(result["independent_reverse_ideal_inclusion_certified"], "Missing n6 completeness evidence.")
        require(Fraction(result["maximum"]) == Fraction(6**15, 5**10), "Wrong n6 maximum.")
        source = read_json(base / "source_manifest.json")
        for name, expected in source["sha256"].items():
            if name == "singular_runtime.json":
                continue  # Machine-path metadata was explicitly sanitized.
            require(digest(base / name) == expected, f"n6 source binding failed: {name}")
        return {"kind": "saved-computer-assisted-proof", "scope": "Full n6 theorem; fresh CAS regeneration is not performed by an audit."}
    if case == "n7":
        result = read_json(base / "classification_based_certificate.json")
        require(result["twelve_distinct_orbits"] and result["all_other_orbits_below_candidate"], "Incomplete n7 comparison.")
        require(len(result["certified_additional_orbits"]) == 10, "Wrong n7 orbit count.")
        require(not result["global_completeness_source"]["independently_recomputed"], "Misstated classification scope.")
        source = read_json(base / "source_manifest.json")
        for name, expected in source["sha256"].items():
            path = base / ("original/certify_twelve.py" if name == "certify_twelve.py" else name)
            require(digest(path) == expected, f"n7 source binding failed: {name}")
        return {"kind": "cited-classification-plus-certified-comparison", "scope": "The published complete seven-vortex classification remains an external premise."}
    if case == "n8":
        data = base / "data"
        result = read_json(data / "FINAL_CERTIFICATE.json")
        cover = read_json(data / "global_pair_bound_bernstein_frontier.json")
        coefficient_hash = digest(data / "global_pair_bound_exact_contacts.json")
        require(result["global_majorant_proved"] and result["all_required_computational_checks_passed"], "Incomplete n8 certificate.")
        require(result["unresolved_boxes"] == 0 and cover["frontier"] == [] and cover["global_majorant_proved"], "Unresolved n8 cover.")
        require(result["coefficient_sha256"] == cover["coefficient_sha256"] == coefficient_hash, "Wrong n8 coefficient binding.")
        require(result["cover_counts"] == cover["counts"], "Inconsistent n8 cover counts.")
        counts = cover["counts"]
        require(counts["visited"] == 2 * counts["split"] + 1, "Invalid n8 tree count.")
        require(sum(counts[k] for k in ["outside", "local", "positive"]) == counts["split"] + 1, "Invalid n8 leaf count.")
        for name, expected in result["files_sha256"].items():
            require(digest(base / name) == expected, f"n8 verifier binding failed: {name}")
        return {"kind": "saved-full-cover", "unresolved_boxes": 0, "scope": "Stored n8 computational premises checked; no fresh full cover at audit level."}
    if case == "n9":
        result = read_json(base / "FINAL_CERTIFICATE_AUDIT.json")
        fresh = read_json(base / "FRESH_VERIFICATION.json")
        cover = read_json(base / "global_pair_bound_bernstein_frontier.json")
        coefficient_hash = digest(base / "global_pair_bound_exact_contacts.json")
        require(result["fresh_complete_cover_verified"] and result["partition_tree_conservation_verified"], "Incomplete n9 audit.")
        require(fresh["fresh_full_cover_passed"] and fresh["unresolved_boxes"] == 0, "Incomplete n9 saved replay.")
        require(cover["global_majorant_proved"] and cover["frontier"] == [] and cover["strict_auxiliary_counterexample"] is None, "Unresolved n9 cover.")
        require(result["coefficient_sha256"] == fresh["coefficient_sha256"] == cover["coefficient_sha256"] == coefficient_hash, "Wrong n9 coefficient binding.")
        counts = cover["counts"]
        require(counts == fresh["counts"] and counts["visited"] == result["visited_boxes"], "Inconsistent n9 counts.")
        require(counts["visited"] == 2 * counts["split"] + 1, "Invalid n9 tree count.")
        leaves = sum(counts.get(key, 0) for key in N9_LEAF_REASONS)
        require(leaves == counts["split"] + 1 == result["certified_leaves"], "Invalid n9 leaf count.")
        source = read_json(base / "source_manifest.json")
        for name, expected in source["inputs"].items():
            path = base / name
            if path.is_file():
                require(digest(path) == expected, f"n9 source binding failed: {name}")
        return {"kind": "saved-full-cover", "unresolved_boxes": 0, "scope": "Core n9 theorem; the independent website-source appendix is not bundled or rechecked."}
    raise RuntimeError(f"Unknown case: {case}")


CHECK_SCRIPTS = {
    "n6": ["verify_global.py"],
    "n7": ["certify_twelve.py"],
    "n8": ["verify_radius_bounds.py", "verify_exact_definition.py", "verify_positive_definiteness.py", "verify_contact_neighborhoods.py"],
    "n9": ["verify_basics.py", "verify_fourth_moment_bound.py", "verify_discrete_radial_remainder.py", "check_arb_bernstein.py", "check_physical_boundary_bernstein.py", "verify_pair_bound_definition.py", "verify_pair_bound_local_preconditioned.py"],
}


def run_case(case: str, level: str, root: Path = ROOT) -> dict:
    if case in {"n2-n5", "n10"}:
        return audit_case(case, root)
    work = root / "build/verification" / f"{case}-{uuid.uuid4().hex[:12]}"
    require(work.resolve().is_relative_to((root / "build/verification").resolve()), "Invalid work directory.")
    shutil.copytree(root / "verification" / case, work, ignore=shutil.ignore_patterns("__pycache__"))

    def run(script: str, *args: str) -> None:
        log = work / (Path(script).stem + ".run.log")
        with log.open("w", encoding="utf-8") as output:
            result = subprocess.run([sys.executable, "-B", str(work / script), *args], cwd=work, stdout=output, stderr=subprocess.STDOUT, timeout=1800)
        require(result.returncode == 0, f"{case}/{script} failed; inspect {log.relative_to(root)}")

    if level == "replay" and case == "n8":
        run("verify_all.py")
        result = read_json(work / "data/FINAL_CERTIFICATE.json")
        require(result["global_majorant_proved"] and result["unresolved_boxes"] == 0, "n8 replay did not complete.")
        return {"kind": "fresh-full-cover", "unresolved_boxes": 0, "output": str(work.relative_to(root))}
    for script in CHECK_SCRIPTS[case]:
        run(script)
    if case == "n6":
        result = read_json(work / "global_verification.json")
        require(result["global_upper_bound_certified"] and result["all_equality_cases_classified"], "n6 exact checks did not complete.")
    elif case == "n7":
        result = read_json(work / "classification_based_certificate.json")
        require(result["twelve_distinct_orbits"] and result["all_other_orbits_below_candidate"], "n7 exact comparison failed.")
        require(not result["global_completeness_source"]["independently_recomputed"], "The classification must remain cited.")
    elif case == "n8":
        result = read_json(work / "data/global_pair_bound_local_certificate.json")
        require(result["local_positivity_proved"], "n8 contact check failed.")
    elif case == "n9":
        result = read_json(work / "global_pair_bound_local_preconditioned_certificate.json")
        require(result["all_matrices_positive_definite"] and result["local_positivity_proved"], "n9 contact check failed.")
        if level == "replay":
            run("verify_pair_bound_cover.py", "1800")
            result = read_json(work / "global_pair_bound_bernstein_frontier.json")
            require(result["global_majorant_proved"] and not result["frontier"] and result["strict_auxiliary_counterexample"] is None, "n9 full cover is incomplete.")
            counts = result["counts"]
            require(counts["visited"] == 2 * counts["split"] + 1, "Invalid fresh n9 tree count.")
            require(sum(counts.get(key, 0) for key in N9_LEAF_REASONS) == counts["split"] + 1, "Invalid fresh n9 leaf count.")
            return {"kind": "fresh-full-cover", "unresolved_boxes": 0, "output": str(work.relative_to(root))}
    scope = "Exact post-CAS checks; saved CAS completeness evidence is reused." if case == "n6" else "Exact comparison; the published complete classification remains cited." if case == "n7" else "Fresh algebra, positivity and contact checks; the complete cover is not rerun."
    return {"kind": "fresh-check", "scope": scope, "output": str(work.relative_to(root))}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", choices=("all",) + CASES, default="all")
    parser.add_argument("--level", choices=("audit", "check", "replay"), default="audit")
    parser.add_argument("--json", action="store_true", help="Print a machine-readable report.")
    args = parser.parse_args(argv)
    try:
        require(__debug__, "Run without Python -O: the inherited proof checks require assertions.")
        file_count = audit_files()
        cases = CASES if args.case == "all" else (args.case,)
        results = {case: audit_case(case) for case in cases}
        if args.level != "audit":
            results = {case: run_case(case, args.level) for case in cases}
        report = {"passed": True, "level": args.level, "files_checked": file_count, "cases": results}
        if args.json:
            print(json.dumps(report, ensure_ascii=False, indent=2))
        else:
            print(f"PASS: {file_count} distributed-file checksums; level={args.level}.")
            for case, result in results.items():
                print(f"  {case}: {result.get('kind', 'exact-integer-comparison')}")
            if args.level == "audit":
                print("Stored evidence audited. Full covers and external classification were not regenerated.")
        return 0
    except (RuntimeError, OSError, KeyError, ValueError, subprocess.TimeoutExpired) as error:
        if args.json:
            print(json.dumps({"passed": False, "level": args.level, "error": str(error)}, ensure_ascii=False))
        else:
            print(f"FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
