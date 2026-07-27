import copy
import hashlib
import json
import subprocess
import tempfile
import unittest
from pathlib import Path

from paired_native import (
    EXPECTED_TIMING_POLICY,
    begin_session,
    complete_reruns,
    finalize_without_measurement,
    load_checkpoint,
    parse_levels,
    parse_timing_policy,
    planned_cells,
    prepare_reruns,
    relevant_link_input_hashes,
    response_link_flags,
    source_fingerprint,
    validate_checkpoint,
    validate_paths,
    validate_row,
)


def row(pattern="corpus/file", level=1, size=100, out_size=40):
    return {
        "compressor": "native",
        "pattern": pattern,
        "size": size,
        "level": level,
        "out_size": out_size,
        "ratio": round(out_size / size, 4),
        "compress_mbps": 12.5,
        "decompress_mbps": 30.0 if level <= 9 else None,
    }


def checkpoint_fixture():
    keys = planned_cells(["corpus/file"], (1, 10))
    identity = {
        "protocol_version": 3,
        "private_cookie_required": True,
        "sentinel": {"binary": "abc"},
    }
    sessions = [
        {
            "id": 0,
            "started": "2026-01-01T00:00:00+00:00",
            "finished": None,
            "core_scheduling_cookie": "0x1234",
            "completed_cells_at_start": 0,
            "completed_cells_at_end": None,
        }
    ]
    state = {
        **identity,
        "started": "2026-01-01T00:00:00+00:00",
        "finished": None,
        "sessions": sessions,
        "pending_rerun_cells": [],
        "rerun_history": [],
        "cells": {
            "corpus/file|1": {
                "order": ["before", "after"],
                "session": 0,
                "elapsed_seconds": 1.25,
                "before": row(),
                "after": row(),
            }
        },
    }
    return identity, keys, {"corpus/file": 100}, state


class PairedNativeTests(unittest.TestCase):
    def test_committed_campaign_manifest_is_complete_and_auditable(self):
        path = (
            Path(__file__).resolve().parent
            / "results/archive/paired-native.88ed5fa0-54b38299.chungus2.manifest.json"
        )
        self.assertEqual(
            hashlib.sha256(path.read_bytes()).hexdigest(),
            "ee3f9be3d9a84cec7b7a45c5fe2afc53c68273779ef007fa770c5a0f1e6dc03b",
        )
        manifest = json.loads(path.read_text(encoding="utf-8"))
        patterns = sorted(manifest["input_size"])
        levels = tuple(manifest["levels"])
        keys = planned_cells(patterns, levels)
        validate_checkpoint(
            manifest,
            {
                "protocol_version": 3,
                "private_cookie_required": True,
            },
            keys,
            manifest["input_size"],
        )
        self.assertEqual(levels, tuple(range(1, 11)))
        self.assertEqual(len(patterns), 23)
        self.assertEqual(len(manifest["cells"]), 230)
        self.assertEqual(manifest["pending_rerun_cells"], [])
        self.assertEqual(
            [entry["cells"] for entry in manifest["rerun_history"]],
            [["silesia/mozilla|1"], ["silesia/mozilla|1"]],
        )
        first_roles = [cell["order"][0] for cell in manifest["cells"].values()]
        self.assertEqual(first_roles.count("before"), 115)
        self.assertEqual(first_roles.count("after"), 115)
        self.assertEqual(
            manifest["before"]["commit"],
            "88ed5fa052468d95df28087d0eb825b0aa50eced",
        )
        self.assertTrue(manifest["before"]["dirty"])
        self.assertEqual(
            manifest["after"]["commit"],
            "54b38299fa43af22d450ba76b0351ec89b61d3a1",
        )
        self.assertFalse(manifest["after"]["dirty"])
        self.assertEqual(manifest["cells"]["silesia/mozilla|1"]["session"], 2)

    def test_response_link_flags_excludes_objects_and_keeps_flag_arguments(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "checkout"
            root.mkdir()
            response = root / "bench-report.rsp"
            response.write_text(
                "\n".join(
                    (
                        f'"{root}/Bench.c.o.export"',
                        '"-L"',
                        '"/toolchain/lib"',
                        '"--sysroot"',
                        '"/toolchain"',
                        '"-Xlinker"',
                        '"--build-id=sha1"',
                        '"-Lrust/miniz_oxide_shim/target/release"',
                        '"-lminiz_oxide_shim"',
                        '"-flto"',
                        '"-O3"',
                    )
                )
                + "\n",
                encoding="utf-8",
            )
            self.assertEqual(
                response_link_flags(response, root),
                [
                    "-L",
                    "/toolchain/lib",
                    "--sysroot",
                    "/toolchain",
                    "-Xlinker",
                    "--build-id=sha1",
                    "-Lrust/miniz_oxide_shim/target/release",
                    "-lminiz_oxide_shim",
                    "-flto",
                    "-O3",
                ],
            )

    def test_response_link_flags_rejects_missing_argument(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            response = root / "bench-report.rsp"
            response.write_text('"-L"\n', encoding="utf-8")
            with self.assertRaisesRegex(RuntimeError, "unterminated link flag"):
                response_link_flags(response, root)

    def test_parse_levels_is_strict_and_unique(self):
        self.assertEqual(parse_levels("1, 9,10"), (1, 9, 10))
        for invalid in ("", "1,", ",1", "1,,2", "1,nope", "0", "11", "1,1"):
            with self.subTest(invalid=invalid):
                with self.assertRaises(RuntimeError):
                    parse_levels(invalid)

    def test_binary_timing_policy_contract_is_exact(self):
        self.assertEqual(parse_timing_policy(EXPECTED_TIMING_POLICY), EXPECTED_TIMING_POLICY)
        for invalid in (
            {"timing_aggregation": "median", "timing_reps": 3},
            {"timing_aggregation": "mean", "timing_reps": 5},
            {"timing_aggregation": "median", "timing_reps": True},
            ["median", 5],
        ):
            with self.subTest(invalid=invalid):
                with self.assertRaises(RuntimeError):
                    parse_timing_policy(invalid)

    def test_checkerboard_balances_each_level(self):
        patterns = [f"c/f{i}" for i in range(23)]
        keys = planned_cells(patterns, (1, 2, 10))
        for level in (1, 2, 10):
            first = [order[0] for _pattern, cell_level, order in keys if cell_level == level]
            self.assertEqual({first.count("before"), first.count("after")}, {11, 12})
        self.assertEqual(keys[0][2], ("before", "after"))
        self.assertEqual(keys[1][2], ("after", "before"))

    def test_outputs_are_distinct_and_outside_roots(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp).resolve()
            before = base / "before"
            after = base / "after"
            before.mkdir()
            after.mkdir()
            validate_paths(
                before,
                after,
                base / "out-before.json",
                base / "out-after.json",
                base / "manifest.json",
            )
            with self.assertRaisesRegex(RuntimeError, "outside both roots"):
                validate_paths(
                    before,
                    after,
                    before / "out.json",
                    base / "out-after.json",
                    base / "manifest.json",
                )
            with self.assertRaisesRegex(RuntimeError, "must be distinct"):
                validate_paths(
                    before,
                    after,
                    base / "same.json",
                    base / "same.json",
                    base / "manifest.json",
                )

    def test_row_validation_checks_numbers_size_ratio_and_decode_policy(self):
        self.assertEqual(validate_row(row(), "corpus/file", 1, 100), row())
        self.assertEqual(
            validate_row(row(level=10), "corpus/file", 10, 100), row(level=10)
        )
        mutations = (
            ("size", 99),
            ("ratio", 0.9),
            ("compress_mbps", float("nan")),
            ("decompress_mbps", -1.0),
        )
        for field, value in mutations:
            bad = row()
            bad[field] = value
            with self.subTest(field=field):
                with self.assertRaises(RuntimeError):
                    validate_row(bad, "corpus/file", 1, 100)

    def test_resume_accepts_a_new_private_cookie_and_records_session(self):
        identity, keys, sizes, state = checkpoint_fixture()
        validate_checkpoint(state, identity, keys, sizes)
        second = begin_session(state, "0xabcd", "2026-01-02T00:00:00+00:00")
        self.assertEqual(second, 1)
        self.assertEqual(
            state["sessions"][0]["interrupted_before"],
            "2026-01-02T00:00:00+00:00",
        )
        self.assertEqual(state["sessions"][1]["core_scheduling_cookie"], "0xabcd")
        validate_checkpoint(state, identity, keys, sizes)

    def test_rerun_cell_is_idempotent_across_interrupted_resumes(self):
        identity, keys, sizes, state = checkpoint_fixture()
        valid = {"corpus/file|1", "corpus/file|10"}
        prepare_reruns(state, ["corpus/file|1"], valid)
        self.assertNotIn("corpus/file|1", state["cells"])
        self.assertEqual(state["pending_rerun_cells"], ["corpus/file|1"])

        # Repeating the command while the replacement cell is still absent is
        # a no-op, not a missing-cell error.
        prepare_reruns(state, ["corpus/file|1"], valid)
        self.assertEqual(state["pending_rerun_cells"], ["corpus/file|1"])

        replacement = {
            "order": ["before", "after"],
            "session": 0,
            "elapsed_seconds": 1.0,
            "before": row(),
            "after": row(),
        }
        state["cells"]["corpus/file|1"] = replacement
        # Repeating after the cell was checkpointed must not delete it again.
        prepare_reruns(state, ["corpus/file|1"], valid)
        self.assertIn("corpus/file|1", state["cells"])

        complete_reruns(state, "2026-01-02T01:00:00+00:00")
        self.assertEqual(state["pending_rerun_cells"], [])
        self.assertEqual(state["rerun_history"][0]["cells"], ["corpus/file|1"])
        validate_checkpoint(state, identity, keys, sizes)

    def test_finished_noop_resume_does_not_mutate_provenance(self):
        identity, keys, sizes, state = checkpoint_fixture()
        state["cells"]["corpus/file|10"] = {
            "order": ["after", "before"],
            "session": 0,
            "elapsed_seconds": 2.0,
            "before": row(level=10),
            "after": row(level=10),
        }
        self.assertTrue(
            finalize_without_measurement(state, "2026-01-02T00:00:00+00:00")
        )
        validate_checkpoint(state, identity, keys, sizes)
        snapshot = copy.deepcopy(state)
        self.assertFalse(
            finalize_without_measurement(state, "2026-01-03T00:00:00+00:00")
        )
        self.assertEqual(state, snapshot)

    def test_checkpoint_rejects_unknown_cell_order_and_corrupt_finish(self):
        identity, keys, sizes, state = checkpoint_fixture()
        unknown = copy.deepcopy(state)
        unknown["cells"]["corpus/other|1"] = unknown["cells"]["corpus/file|1"]
        with self.assertRaisesRegex(RuntimeError, "unknown cells"):
            validate_checkpoint(unknown, identity, keys, sizes)

        wrong_order = copy.deepcopy(state)
        wrong_order["cells"]["corpus/file|1"]["order"] = ["after", "before"]
        with self.assertRaisesRegex(RuntimeError, "order mismatch"):
            validate_checkpoint(wrong_order, identity, keys, sizes)

        bad_finish = copy.deepcopy(state)
        bad_finish["finished"] = "2026-01-01T01:00:00+00:00"
        with self.assertRaisesRegex(RuntimeError, "missing cells"):
            validate_checkpoint(bad_finish, identity, keys, sizes)

    def test_checkpoint_loader_rejects_nonfinite_json(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "manifest.json"
            path.write_text('{"x": NaN}\n', encoding="utf-8")
            with self.assertRaisesRegex(RuntimeError, "invalid checkpoint JSON"):
                load_checkpoint(path)
            path.write_text('{"x": 1, "x": 2}\n', encoding="utf-8")
            with self.assertRaisesRegex(RuntimeError, "duplicate JSON object key"):
                load_checkpoint(path)

    def test_source_fingerprint_tracks_diff_and_untracked_bytes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            tracked = root / "tracked.txt"
            tracked.write_text("one\n", encoding="utf-8")
            subprocess.run(["git", "-C", str(root), "add", "tracked.txt"], check=True)
            subprocess.run(
                [
                    "git",
                    "-C",
                    str(root),
                    "-c",
                    "user.name=Benchmark Test",
                    "-c",
                    "user.email=benchmark@example.invalid",
                    "commit",
                    "-qm",
                    "fixture",
                ],
                check=True,
            )
            clean = source_fingerprint(root)
            self.assertFalse(clean["dirty"])
            tracked.write_text("two\n", encoding="utf-8")
            changed = source_fingerprint(root)
            self.assertTrue(changed["dirty"])
            self.assertNotEqual(clean["diff_head_sha256"], changed["diff_head_sha256"])
            untracked = root / "new.txt"
            untracked.write_text("first\n", encoding="utf-8")
            first = source_fingerprint(root)
            untracked.write_text("second\n", encoding="utf-8")
            second = source_fingerprint(root)
            self.assertNotEqual(
                first["untracked_content_sha256"], second["untracked_content_sha256"]
            )

    def test_relevant_inputs_include_actual_miniz_archive(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paths = (
                "bench/ZipBenchReport.lean",
                "bench/Bench/ReportTiming.lean",
                "bench/.lake/build/ir/ZipBenchReport.c.o.export",
                "bench/.lake/build/ir/Bench/ReportTiming.c.o.export",
                "bench/.lake/build/lib/libminiz_oxide_ffi.a",
                "bench/.lake/build/lib/liblibdeflate_ffi.a",
                "bench/.lake/build/lib/libzopfli_ffi.a",
                "bench/rust/miniz_oxide_shim/target/release/libminiz_oxide_shim.a",
            )
            for index, relative in enumerate(paths):
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(f"fixture-{index}".encode())
            hashes = relevant_link_input_hashes(
                root,
                ["-Lrust/miniz_oxide_shim/target/release", "-lminiz_oxide_shim"],
            )
            self.assertIn("miniz_oxide_shim", hashes)
            self.assertEqual(
                hashes["miniz_oxide_shim"],
                hashlib.sha256(b"fixture-7").hexdigest(),
            )


if __name__ == "__main__":
    unittest.main()
