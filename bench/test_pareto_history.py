import unittest

import pareto_history


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

    def test_ticker_preserves_protocol_while_bounding_width(self):
        text = pareto_history.ticker_text(
            frame("migration", "median-of-5", True), 42, 43
        )
        self.assertLessEqual(len(text), 102)
        self.assertIn("[median-of-5]", text)
        self.assertTrue(text.endswith("…"))


if __name__ == "__main__":
    unittest.main()
