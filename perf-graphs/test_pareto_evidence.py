from __future__ import annotations

import contextlib
import io
import json
from pathlib import Path
import sys
import tempfile
import types
import unittest
from unittest import mock


# The numerical and report tests do not render with matplotlib.  Keep them
# runnable in a plain Python environment as well as the project's nix shell.
try:
    import matplotlib  # noqa: F401
except ModuleNotFoundError:
    matplotlib_stub = types.ModuleType("matplotlib")
    matplotlib_stub.use = lambda _backend: None
    pyplot_stub = types.ModuleType("matplotlib.pyplot")
    sys.modules["matplotlib"] = matplotlib_stub
    sys.modules["matplotlib.pyplot"] = pyplot_stub

import pareto_evidence as pe


def point(level: int, ratio: float, speed: float) -> pe.AggregatePoint:
    return pe.AggregatePoint(level, ratio, speed, 1)


class FrontierMathTests(unittest.TestCase):
    def test_lower_hull_drops_interior_and_right_dominated_points(self):
        hull = pe.achievable_frontier(
            [
                point(1, 0.10, 10.0),
                point(2, 0.20, 12.5),  # above the A--C line in time space
                point(3, 0.30, 20.0),
                point(4, 0.40, 16.0),  # right of the globally fastest point
            ]
        )

        self.assertEqual([p.labels for p in hull], [("L1",), ("L3",)])
        self.assertAlmostEqual(pe.time_at_or_below_ratio(hull, 0.20), 0.075)
        self.assertTrue(math_is_inf(pe.time_at_or_below_ratio(hull, 0.09)))
        self.assertAlmostEqual(pe.time_at_or_below_ratio(hull, 0.40), 0.05)

    def test_equal_ratio_keeps_fastest_point(self):
        hull = pe.achievable_frontier(
            [point(1, 0.25, 10.0), point(2, 0.25, 20.0)]
        )
        self.assertEqual(len(hull), 1)
        self.assertEqual(hull[0].labels, ("L2",))
        self.assertAlmostEqual(hull[0].speed, 20.0)

    def test_frontier_comparison_checks_union_of_breakpoints(self):
        before = pe.achievable_frontier(
            [point(1, 0.10, 10.0), point(3, 0.30, 20.0)]
        )
        improved = pe.achievable_frontier(
            [point(1, 0.10, 11.0), point(2, 0.20, 16.0), point(3, 0.30, 22.0)]
        )
        passed, rows = pe.compare_frontiers(before, improved, 0.0)
        self.assertTrue(passed)
        self.assertIn(0.20, [row[0] for row in rows])

        regressed = pe.achievable_frontier(
            [point(1, 0.10, 9.0), point(3, 0.30, 22.0)]
        )
        passed, rows = pe.compare_frontiers(before, regressed, 0.0)
        self.assertFalse(passed)
        self.assertAlmostEqual(rows[0][3], 0.9)


class InputPrimitiveTests(unittest.TestCase):
    def test_ratio_prefers_exact_sizes_and_falls_back_when_absent(self):
        self.assertAlmostEqual(
            pe.row_ratio({"size": 3, "out_size": 1, "ratio": 0.999999}),
            1.0 / 3.0,
        )
        self.assertEqual(pe.row_ratio({"ratio": 0.25}), 0.25)

    def test_median5_requires_structured_exact_policy(self):
        def doc(meta):
            return pe.Document(Path("input.json"), "0" * 64, meta, [])

        self.assertTrue(
            pe.median5_verified(
                doc({"timing_aggregation": "Median", "timing_reps": 5})
            )
        )
        self.assertFalse(pe.median5_verified(doc({"note": "median-of-5"})))
        self.assertFalse(
            pe.median5_verified(
                doc({"timing_aggregation": "mean", "timing_reps": 5})
            )
        )
        self.assertFalse(
            pe.median5_verified(
                doc({"timing_aggregation": "median", "timing_reps": "5"})
            )
        )

    def test_nonfinite_or_negative_frontier_tolerance_is_rejected_early(self):
        for value in ("nan", "inf", "-1"):
            with self.subTest(value=value):
                with self.assertRaisesRegex(ValueError, "finite and nonnegative"):
                    pe.run(
                        [
                            "missing-refs.json",
                            "missing-before.json",
                            "missing-after.json",
                            "-o",
                            "missing-output",
                            "--frontier-tolerance-pct",
                            value,
                        ]
                    )


def math_is_inf(value: float) -> bool:
    return value == float("inf")


class EndToEndAuditTests(unittest.TestCase):
    META = {
        "date": "2026-07-27T00:00:00Z",
        "machine": "Linux test-host x86_64",
        "git_commit": "deadbeef",
        "toolchain": "leanprover/lean4:v4.test",
        "timing_aggregation": "median",
        "timing_reps": 5,
    }

    @staticmethod
    def row(compressor: str, level: int, out_size: int, speed: float) -> dict:
        return {
            "compressor": compressor,
            "pattern": "silesia/sample",
            "size": 1000,
            "level": level,
            "out_size": out_size,
            # Deliberately wrong: the audit must reconstruct out_size / size.
            "ratio": 0.999999,
            "compress_mbps": speed,
        }

    def write_inputs(
        self,
        root: Path,
        *,
        failing_miniz_level: int | None = None,
        missing_miniz_level: int | None = None,
        all_miniz_invalid: bool = False,
        partial_native: bool = False,
        omit_paired_metadata: bool = False,
        before_meta_overrides: dict | None = None,
        after_meta_overrides: dict | None = None,
    ) -> tuple[Path, Path, Path]:
        root.mkdir(parents=True)
        native = [
            self.row(
                "native",
                level,
                410 - 10 * level,
                210.0 - 10.0 * level,
            )
            for level in range(1, 11)
        ]
        if partial_native:
            native = native[:-1]
        miniz = []
        for level in range(1, 10):
            if level == missing_miniz_level:
                continue
            speed = 0.0 if all_miniz_invalid else 150.0
            if level == failing_miniz_level:
                speed = 250.0
            miniz.append(self.row("miniz_oxide", level, 450, speed))
        refs = miniz + [
            self.row("zlib", 1, 460, 140.0),
            self.row("zlib_rs", 1, 470, 130.0),
        ]
        paired = {
            "pairing": pe.PAIRING,
            "order_scheme": pe.ORDER_SCHEME,
            "cpu_affinity": [7],
            # A resumed protocol-v3 run may legitimately have a distinct
            # private cookie per benchmark session.
            "core_scheduling_cookies": ["0x1234", "0x5678"],
            "benchmark_sessions": 2,
            "benchmark_harness_sha256": "c" * 64,
            "benchmark_driver_sha256": "d" * 64,
            "controlled_link_layout_sha256": "e" * 64,
            "relevant_link_inputs_sha256": {
                "harness_source": "f" * 64,
                "harness_object": "1" * 64,
                "miniz_oxide_ffi": "2" * 64,
            },
            "link_flags_sha256": "3" * 64,
            "link_response_layout_sha256": "4" * 64,
        }
        before_meta = dict(self.META)
        after_meta = dict(self.META)
        if not omit_paired_metadata:
            before_meta.update(paired)
            after_meta.update(paired)
            # The two executables are expected to differ; each must only be
            # individually pinned by a valid digest.
            before_meta["benchmark_binary_sha256"] = "a" * 64
            after_meta["benchmark_binary_sha256"] = "b" * 64
        before_meta.update(before_meta_overrides or {})
        after_meta.update(after_meta_overrides or {})
        documents = {
            "refs.json": {"meta": self.META, "results": refs},
            "before.json": {"meta": before_meta, "results": native},
            "after.json": {"meta": after_meta, "results": native},
        }
        for name, payload in documents.items():
            (root / name).write_text(
                json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n",
                encoding="utf-8",
            )
        return root / "refs.json", root / "before.json", root / "after.json"

    @staticmethod
    def fake_render_graph(*, corpus, metric, outdir, **_kwargs):
        path = outdir / f"perf_before_after_{metric}_{corpus}.png"
        path.write_bytes(b"deterministic test PNG\n")
        return path

    def run_audit(
        self,
        inputs: tuple[Path, Path, Path],
        outdir: Path,
        *extra_args: str,
    ) -> int:
        argv = [
            *(str(path) for path in inputs),
            "-o",
            str(outdir),
            "--corpora",
            "silesia",
            *extra_args,
        ]
        with mock.patch.object(pe, "render_graph", self.fake_render_graph):
            with contextlib.redirect_stdout(io.StringIO()):
                return pe.run(argv)

    def test_strict_miniz_l1_through_l9_gate_controls_exit(self):
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as temp:
            root = Path(temp)
            passing = self.write_inputs(root / "pass")
            self.assertEqual(self.run_audit(passing, root / "pass-out"), 0)
            report = (root / "pass-out" / "pareto_audit.txt").read_text()
            self.assertIn("evidence mode: FINAL", report)
            self.assertIn("SILESIA MINIZ_OXIDE L1-L9 CONTAINMENT: PASS", report)
            miniz_table = report.split(
                "silesia: native-after relationship to miniz_oxide target levels",
                1,
            )[1].split("\n\n", 1)[0]
            for level in range(1, 10):
                self.assertRegex(miniz_table, rf"(?m)^ L{level}\s")

            failing = self.write_inputs(root / "fail", failing_miniz_level=1)
            self.assertEqual(self.run_audit(failing, root / "fail-out"), 1)
            report = (root / "fail-out" / "pareto_audit.txt").read_text()
            self.assertIn("SILESIA MINIZ_OXIDE L1-L9 CONTAINMENT: FAIL", report)

    def test_missing_miniz_level_is_a_strict_input_error(self):
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as temp:
            root = Path(temp)
            inputs = self.write_inputs(root / "inputs", missing_miniz_level=1)
            with self.assertRaisesRegex(ValueError, "incomplete silesia.*L1"):
                self.run_audit(inputs, root / "out")

    def test_all_invalid_miniz_speeds_cannot_report_pass(self):
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as temp:
            root = Path(temp)
            inputs = self.write_inputs(root / "inputs", all_miniz_invalid=True)
            self.assertEqual(self.run_audit(inputs, root / "out"), 1)
            report = (root / "out" / "pareto_audit.txt").read_text()
            self.assertIn("SILESIA MINIZ_OXIDE L1-L9 CONTAINMENT: FAIL", report)

    def test_audit_is_deterministic_across_parent_directories(self):
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as temp:
            root = Path(temp)
            left = self.write_inputs(root / "left" / "inputs")
            right = self.write_inputs(root / "right" / "inputs")
            self.assertEqual(self.run_audit(left, root / "left" / "out"), 0)
            self.assertEqual(self.run_audit(right, root / "right" / "out"), 0)
            left_report = (root / "left" / "out" / "pareto_audit.txt").read_bytes()
            right_report = (root / "right" / "out" / "pareto_audit.txt").read_bytes()
            self.assertEqual(left_report, right_report)
            self.assertNotIn(str(root).encode(), left_report)
            self.assertIn(b"sha256=", left_report)

    def test_complete_native_l1_l10_is_default_and_smoke_escape_is_explicit(self):
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as temp:
            root = Path(temp)
            inputs = self.write_inputs(root / "partial", partial_native=True)
            with self.assertRaisesRegex(ValueError, "native level coverage"):
                self.run_audit(inputs, root / "strict-out")
            self.assertEqual(
                self.run_audit(
                    inputs,
                    root / "smoke-out",
                    "--allow-legacy-or-partial-inputs",
                ),
                0,
            )
            report = (root / "smoke-out" / "pareto_audit.txt").read_text()
            self.assertIn("evidence mode: SMOKE", report)

    def test_legacy_paired_metadata_requires_smoke_escape(self):
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as temp:
            root = Path(temp)
            legacy = {
                "pairing": "cell-interleaved alternating AB/BA",
                "order_scheme": pe.ORDER_SCHEME,
                "cpu_affinity": [7],
                "core_scheduling_cookie": "0x1234",
                "benchmark_binary_sha256": "a" * 64,
                "benchmark_harness_sha256": "c" * 64,
                "link_flags_sha256": "3" * 64,
                "comparator_archives_sha256": {
                    "miniz_oxide": "5" * 64,
                    "libdeflate": "6" * 64,
                    "zopfli": "7" * 64,
                },
            }
            inputs = self.write_inputs(
                root / "legacy",
                omit_paired_metadata=True,
                before_meta_overrides=legacy,
                after_meta_overrides=legacy,
            )
            with self.assertRaisesRegex(ValueError, "paired metadata field"):
                self.run_audit(inputs, root / "strict-out")
            self.assertEqual(
                self.run_audit(
                    inputs,
                    root / "smoke-out",
                    "--allow-legacy-or-partial-inputs",
                ),
                0,
            )

    def test_hardened_paired_metadata_rejects_bad_or_mismatched_fields(self):
        link_input_mismatch = {
            "harness_source": "f" * 64,
            "harness_object": "1" * 64,
            "miniz_oxide_ffi": "8" * 64,
        }
        cases = (
            ("order", {"order_scheme": "alternating only"}, {}, "order_scheme"),
            ("cpus", {"cpu_affinity": [7, 8]}, {}, "exactly one"),
            (
                "zero-cookie",
                {"core_scheduling_cookies": ["0x0", "0x5678"]},
                {},
                "nonzero",
            ),
            (
                "cookie-mismatch",
                {},
                {"core_scheduling_cookies": ["0x1234", "0x9abc"]},
                "cookies must match",
            ),
            (
                "session-count",
                {"benchmark_sessions": 1},
                {},
                "length must equal benchmark_sessions",
            ),
            (
                "harness-mismatch",
                {},
                {"benchmark_harness_sha256": "3" * 64},
                "harness_sha256 must match",
            ),
            (
                "driver-mismatch",
                {},
                {"benchmark_driver_sha256": "9" * 64},
                "driver_sha256 must match",
            ),
            (
                "layout-mismatch",
                {},
                {"controlled_link_layout_sha256": "a" * 64},
                "controlled_link_layout_sha256 must match",
            ),
            (
                "link-input-mismatch",
                {},
                {"relevant_link_inputs_sha256": link_input_mismatch},
                "relevant_link_inputs_sha256 must match",
            ),
            (
                "bad-binary-hash",
                {"benchmark_binary_sha256": "not-a-hash"},
                {},
                "binary_sha256 must be a SHA-256",
            ),
            (
                "bad-driver-hash",
                {"benchmark_driver_sha256": "not-a-hash"},
                {},
                "driver_sha256 must be a SHA-256",
            ),
            (
                "bad-link-input-hash",
                {
                    "relevant_link_inputs_sha256": {
                        "harness_source": "not-a-hash"
                    }
                },
                {},
                "name-to-SHA-256 mapping",
            ),
        )
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as temp:
            root = Path(temp)
            for name, before_overrides, after_overrides, message in cases:
                with self.subTest(name=name):
                    inputs = self.write_inputs(
                        root / name,
                        before_meta_overrides=before_overrides,
                        after_meta_overrides=after_overrides,
                    )
                    with self.assertRaisesRegex(ValueError, message):
                        self.run_audit(inputs, root / f"{name}-out")


if __name__ == "__main__":
    unittest.main()
