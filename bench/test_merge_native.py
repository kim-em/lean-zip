import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import pareto_history
import plot


HERE = Path(__file__).resolve().parent


def document(commit, rows, **extra_meta):
    return {
        "meta": {
            "date": f"date-{commit}",
            "machine": "fixture",
            "git_commit": commit,
            "toolchain": "fixture-toolchain",
            "timing_aggregation": "median",
            "timing_reps": 5,
            **extra_meta,
        },
        "results": rows,
    }


def row(compressor, pattern, level, speed):
    return {
        "compressor": compressor,
        "pattern": pattern,
        "size": 100,
        "level": level,
        "out_size": 40,
        "ratio": 0.4,
        "compress_mbps": speed,
        "decompress_mbps": 20.0,
    }


def run_merge(old_path, new_path, out_path, *, check=True):
    return subprocess.run(
        [
            sys.executable,
            str(HERE / "merge_native.py"),
            str(old_path),
            str(new_path),
            str(out_path),
        ],
        check=check,
        capture_output=True,
        text=True,
    )


class MergeNativeTests(unittest.TestCase):
    def test_scopes_fresh_metadata_and_retains_reused_provenance(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            old_path = root / "old.json"
            new_path = root / "new.json"
            out_path = root / "out.json"
            old = document(
                "old",
                [
                    row("native", "c/a", 1, 1.0),
                    row("zlib", "c/a", 1, 2.0),
                ],
                old_session="kept",
            )
            new = document(
                "new",
                [row("native", "c/a", 1, 3.0)],
                pairing="checkerboard",
                private_cookie="0x1234",
            )
            old_path.write_text(json.dumps(old), encoding="utf-8")
            new_path.write_text(json.dumps(new), encoding="utf-8")

            run_merge(old_path, new_path, out_path)
            merged = json.loads(out_path.read_text(encoding="utf-8"))

            rows = {
                (item["compressor"], item["pattern"], item["level"]): item
                for item in merged["results"]
            }
            self.assertEqual(rows[("native", "c/a", 1)]["compress_mbps"], 3.0)
            self.assertEqual(rows[("zlib", "c/a", 1)]["compress_mbps"], 2.0)

            meta = merged["meta"]
            self.assertEqual(meta["git_commit"], "new")
            self.assertEqual(meta["timing_aggregation"], "median")
            self.assertEqual(meta["timing_reps"], 5)
            self.assertNotIn("pairing", meta)
            provenance = meta["row_provenance"]
            self.assertEqual(provenance["schema_version"], 1)
            self.assertEqual(provenance["fresh_keys"], [["native", "c/a", 1]])
            fresh, reused = provenance["groups"]
            self.assertEqual(fresh["input_role"], "fresh")
            self.assertEqual(fresh["keys"], [["native", "c/a", 1]])
            self.assertEqual(fresh["row_count"], 1)
            self.assertEqual(fresh["meta"]["pairing"], "checkerboard")
            self.assertEqual(reused["input_role"], "reused")
            self.assertEqual(reused["row_count"], 1)
            self.assertEqual(reused["meta"]["old_session"], "kept")
            self.assertEqual(
                provenance["merge_inputs"]["fresh"]["sha256"],
                hashlib.sha256(new_path.read_bytes()).hexdigest(),
            )
            self.assertEqual(
                provenance["merge_inputs"]["reused"]["sha256"],
                hashlib.sha256(old_path.read_bytes()).hexdigest(),
            )

    def test_successive_partial_merges_keep_original_reference_session(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            base_path = root / "base.json"
            n1_path = root / "n1.json"
            n2_path = root / "n2.json"
            once_path = root / "once.json"
            twice_path = root / "twice.json"
            base_path.write_text(json.dumps(document(
                "base",
                [
                    row("native", "c/a", 1, 1.0),
                    row("native", "c/a", 2, 2.0),
                    row("zlib", "c/a", 1, 3.0),
                ],
            )), encoding="utf-8")
            n1_path.write_text(json.dumps(document(
                "n1", [row("native", "c/a", 1, 10.0)]
            )), encoding="utf-8")
            n2_path.write_text(json.dumps(document(
                "n2", [row("native", "c/a", 2, 20.0)]
            )), encoding="utf-8")

            run_merge(base_path, n1_path, once_path)
            run_merge(once_path, n2_path, twice_path)
            merged = json.loads(twice_path.read_text(encoding="utf-8"))
            provenance = merged["meta"]["row_provenance"]

            session_for = {}
            for group in provenance["groups"]:
                self.assertNotIn("row_provenance", group["meta"])
                for row_key in group["keys"]:
                    session_for[tuple(row_key)] = group["meta"]["git_commit"]
            self.assertEqual(
                session_for,
                {
                    ("native", "c/a", 1): "n1",
                    ("native", "c/a", 2): "n2",
                    ("zlib", "c/a", 1): "base",
                },
            )
            label = plot._provenance(merged["meta"])
            self.assertIn("fresh native rows @ n2", label)
            self.assertIn("reused rows across 2 sessions", label)
            self.assertEqual(
                pareto_history.reference_meta(merged["meta"])["git_commit"],
                "base",
            )

    def test_rejects_cross_machine_merge(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            old_path = root / "old.json"
            new_path = root / "new.json"
            out_path = root / "out.json"
            old_path.write_text(json.dumps(document(
                "old", [row("zlib", "c/a", 1, 2.0)]
            )), encoding="utf-8")
            new = document("new", [row("native", "c/a", 1, 3.0)])
            new["meta"]["machine"] = "different fixture"
            new_path.write_text(json.dumps(new), encoding="utf-8")

            result = run_merge(old_path, new_path, out_path, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("different machines", result.stderr)
            self.assertFalse(out_path.exists())

    def test_rejects_missing_measurement_machine(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            old_path = root / "old.json"
            new_path = root / "new.json"
            out_path = root / "out.json"
            old_path.write_text(json.dumps(document(
                "old", [row("zlib", "c/a", 1, 2.0)]
            )), encoding="utf-8")
            new = document("new", [row("native", "c/a", 1, 3.0)])
            new["meta"]["machine"] = None
            new_path.write_text(json.dumps(new), encoding="utf-8")

            result = run_merge(old_path, new_path, out_path, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("must declare their measurement machine", result.stderr)
            self.assertFalse(out_path.exists())

    def test_rejects_duplicate_result_keys(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            old_path = root / "old.json"
            new_path = root / "new.json"
            out_path = root / "out.json"
            old_path.write_text(json.dumps(document(
                "old", [row("zlib", "c/a", 1, 2.0)]
            )), encoding="utf-8")
            duplicate = row("native", "c/a", 1, 3.0)
            new_path.write_text(json.dumps(document(
                "new", [duplicate, dict(duplicate)]
            )), encoding="utf-8")

            result = run_merge(old_path, new_path, out_path, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("duplicate", result.stderr)
            self.assertFalse(out_path.exists())

    def test_rejects_empty_fresh_snapshot(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            old_path = root / "old.json"
            new_path = root / "new.json"
            out_path = root / "out.json"
            old_path.write_text(json.dumps(document(
                "old", [row("zlib", "c/a", 1, 2.0)]
            )), encoding="utf-8")
            new_path.write_text(json.dumps(document("new", [])), encoding="utf-8")

            result = run_merge(old_path, new_path, out_path, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("no freshly measured rows", result.stderr)
            self.assertFalse(out_path.exists())

    def test_rejects_cross_machine_prior_group(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            base_path = root / "base.json"
            n1_path = root / "n1.json"
            n2_path = root / "n2.json"
            once_path = root / "once.json"
            forged_path = root / "forged.json"
            out_path = root / "out.json"
            base_path.write_text(json.dumps(document(
                "base", [row("zlib", "c/a", 1, 2.0)]
            )), encoding="utf-8")
            n1_path.write_text(json.dumps(document(
                "n1", [row("native", "c/a", 1, 3.0)]
            )), encoding="utf-8")
            n2_path.write_text(json.dumps(document(
                "n2", [row("native", "c/a", 2, 4.0)]
            )), encoding="utf-8")
            run_merge(base_path, n1_path, once_path)
            forged = json.loads(once_path.read_text(encoding="utf-8"))
            forged["meta"]["row_provenance"]["groups"][1]["meta"]["machine"] = (
                "different fixture"
            )
            forged_path.write_text(json.dumps(forged), encoding="utf-8")

            result = run_merge(forged_path, n2_path, out_path, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("provenance group 1", result.stderr)
            self.assertIn("different machine", result.stderr)
            self.assertFalse(out_path.exists())

    def test_rejects_non_median_prior_group(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            base_path = root / "base.json"
            n1_path = root / "n1.json"
            n2_path = root / "n2.json"
            once_path = root / "once.json"
            forged_path = root / "forged.json"
            out_path = root / "out.json"
            base_path.write_text(json.dumps(document(
                "base", [row("zlib", "c/a", 1, 2.0)]
            )), encoding="utf-8")
            n1_path.write_text(json.dumps(document(
                "n1", [row("native", "c/a", 1, 3.0)]
            )), encoding="utf-8")
            n2_path.write_text(json.dumps(document(
                "n2", [row("native", "c/a", 2, 4.0)]
            )), encoding="utf-8")
            run_merge(base_path, n1_path, once_path)
            forged = json.loads(once_path.read_text(encoding="utf-8"))
            forged["meta"]["row_provenance"]["groups"][1]["meta"].update({
                "timing_aggregation": "single",
                "timing_reps": 1,
            })
            forged_path.write_text(json.dumps(forged), encoding="utf-8")

            result = run_merge(forged_path, n2_path, out_path, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("old provenance group 1.meta", result.stderr)
            self.assertIn("expected timing_aggregation='median'", result.stderr)
            self.assertFalse(out_path.exists())


if __name__ == "__main__":
    unittest.main()
