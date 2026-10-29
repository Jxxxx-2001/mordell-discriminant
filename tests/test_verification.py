"""Failure checks for the publication boundary, not duplicate theorem tests."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import unittest
import uuid

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("publication_verify", ROOT / "verify.py")
verify = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verify)


class PublicationChecks(unittest.TestCase):
    def fixture(self):
        root = ROOT / "build/tests" / uuid.uuid4().hex
        (root / "verification").mkdir(parents=True)
        data = root / "input.txt"
        data.write_text("exact input", encoding="utf-8")
        (root / "verification/files.sha256.json").write_text(json.dumps({"files": {"input.txt": verify.digest(data)}}), encoding="utf-8")
        return root, data

    def test_corrupted_input_fails(self):
        root, data = self.fixture()
        data.write_text("modified", encoding="utf-8")
        with self.assertRaisesRegex(RuntimeError, "Checksum mismatch"):
            verify.audit_files(root)

    def test_missing_input_fails(self):
        root, data = self.fixture()
        data.unlink()
        with self.assertRaisesRegex(RuntimeError, "Missing distributed file"):
            verify.audit_files(root)

    def test_manifest_cannot_escape_root(self):
        root, data = self.fixture()
        (root / "verification/files.sha256.json").write_text(json.dumps({"files": {"../outside.txt": "0" * 64}}), encoding="utf-8")
        with self.assertRaisesRegex(RuntimeError, "Unsafe manifest path"):
            verify.audit_files(root)

    def test_disabled_assertions_are_rejected(self):
        result = subprocess.run([sys.executable, "-B", "-O", str(ROOT / "verify.py"), "--case", "n10"], capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("without Python -O", result.stderr)

    def test_ten_point_certificate_is_recomputed(self):
        root, _ = self.fixture()
        target = root / "verification/n10"
        target.mkdir()
        original = verify.read_json(ROOT / "verification/n10/exact_counterexample_certificate.json")
        original["P"] = str(int(original["P"]) + 1)
        (target / "exact_counterexample_certificate.json").write_text(json.dumps(original), encoding="utf-8")
        with self.assertRaisesRegex(RuntimeError, "disagrees: P"):
            verify.check_ten(root)


if __name__ == "__main__":
    unittest.main()
