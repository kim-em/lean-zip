import unittest

import pareto_history
import plot


def frame(commit, timing, declared, speed=100.0):
    return {
        "commit": commit,
        "commit_date": "2026-07-25T00:00:00Z",
        "subject": "x" * 200,
        "timing": timing,
        "timing_declared": declared,
        "points": [(1, 0.4, speed)],
    }


class ParetoHistoryTimingTests(unittest.TestCase):
    def test_scoped_provenance_labels_fresh_native_and_reused_references(self):
        meta = {
            "timing_aggregation": "median",
            "timing_reps": 5,
            "frozen_overlays": [{
                "compressor": "zopfli",
                "meta": {
                    "git_commit": "frozen12",
                    "machine": "Linux oldbox x86_64",
                    "timing_aggregation": "single",
                    "timing_reps": 1,
                },
            }],
            "row_provenance": {
                "schema_version": 1,
                "fresh_keys": [["native", "c/a", 1]],
                "groups": [{
                    "input_role": "fresh",
                    "keys": [["native", "c/a", 1]],
                    "meta": {
                        "git_commit": "new12345",
                        "date": "2026-07-27T10:00:00Z",
                        "machine": "Linux fixture x86_64",
                    },
                }, {
                    "input_role": "reused",
                    "keys": [["zlib", "c/a", 1]],
                    "meta": {
                        "git_commit": "old12345",
                        "date": "2026-07-26T10:00:00Z",
                        "machine": "Linux fixture x86_64",
                    }
                }],
            },
        }
        label = plot._provenance(meta)
        self.assertIn("native @ new12345", label)
        self.assertIn("reused refs @ old12345", label)
        self.assertIn(
            "zopfli: frozen single-rep @frozen12/oldbox (indicative)",
            label,
        )
        self.assertIn(
            "routine speed=median-of-5; ratios deterministic\nzopfli:",
            label,
        )
        self.assertEqual(
            pareto_history.reference_meta(meta)["git_commit"], "old12345"
        )

    def test_history_provenance_mentions_only_visible_frozen_overlay(self):
        meta = {
            "ref_commit": "ref12345",
            "ref_date": "2026-07-27",
            "machine": "fixture",
            "history_timing": "median-of-5",
            "frozen_overlays": [{
                "compressor": "zopfli",
                "meta": {
                    "git_commit": "frozen12",
                    "machine": "Linux oldbox x86_64",
                    "timing_aggregation": "single",
                    "timing_reps": 1,
                },
            }],
        }
        label = pareto_history.provenance_of(meta)
        self.assertIn("per-frame routine timing: median-of-5", label)
        self.assertIn("zopfli: frozen single-rep", label)
        self.assertNotIn(
            "zopfli",
            pareto_history.provenance_of({**meta, "frozen_overlays": []}),
        )

    def test_legacy_silesia_is_labelled_single_rep_without_mutating_data(self):
        doc = {"meta": {}, "results": []}
        self.assertEqual(
            pareto_history.frame_timing(doc, "silesia"),
            ("legacy single-rep", False),
        )
        self.assertEqual(doc, {"meta": {}, "results": []})

    def test_declared_routine_frame_is_labelled_median_of_five(self):
        doc = {
            "meta": {"timing_aggregation": "median", "timing_reps": 5},
            "results": [],
        }
        self.assertEqual(
            pareto_history.frame_timing(doc, "silesia"),
            ("median-of-5", True),
        )

    def test_partially_or_incorrectly_declared_frame_fails_visibly(self):
        for meta in (
            {"timing_reps": 5},
            {"timing_aggregation": "median"},
            {"timing_aggregation": "median", "timing_reps": 1},
        ):
            with self.subTest(meta=meta), self.assertRaises(ValueError):
                pareto_history.frame_timing({"meta": meta}, "silesia")

    def test_protocol_transition_survives_noise_filter_and_marks_migration(self):
        frames = [
            frame("legacy1", "legacy single-rep", False),
            frame("migration", "median-of-5", True),
            frame("current", "median-of-5", True),
        ]
        self.assertEqual(pareto_history.drop_noise(frames), frames)
        self.assertEqual(
            pareto_history.history_timing_summary(frames, "silesia"),
            "legacy Silesia single-rep → median-of-5 at migration",
        )

    def test_reference_only_tail_refresh_is_dropped_after_stable_protocol(self):
        frames = [
            frame("first", "median-of-5", True),
            frame("native", "median-of-5", True),
            frame("reference-only", "median-of-5", True),
        ]
        self.assertEqual(pareto_history.drop_noise(frames), frames[:-1])

    def test_ticker_preserves_protocol_while_bounding_width(self):
        text = pareto_history.ticker_text(
            frame("migration", "median-of-5", True), 42, 43
        )
        self.assertLessEqual(len(text), 102)
        self.assertIn("[median-of-5]", text)
        self.assertTrue(text.endswith("…"))


if __name__ == "__main__":
    unittest.main()
