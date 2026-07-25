import unittest
from pathlib import Path

from benchmark_json import (
    load_frozen_zopfli,
    load_routine,
    require_frozen_zopfli,
    require_routine,
    require_routine_if_declared,
)


def routine_doc(reps=5, aggregation="median"):
    return {"meta": {"timing_aggregation": aggregation, "timing_reps": reps}, "results": []}


def zopfli_doc(reps=1, aggregation="single", frozen=True):
    return {
        "meta": {
            "timing_aggregation": aggregation,
            "timing_reps": reps,
            "frozen": frozen,
        },
        "results": [],
    }


class BenchmarkJsonTests(unittest.TestCase):
    def test_routine_requires_exact_median_of_five(self):
        doc = routine_doc()
        self.assertIs(require_routine(doc), doc)
        for bad in (None, 1, "5", 5.0, True):
            with self.subTest(reps=bad), self.assertRaises(ValueError):
                require_routine(routine_doc(reps=bad))
        with self.assertRaises(ValueError):
            require_routine(routine_doc(aggregation="single"))
        with self.assertRaises(ValueError):
            require_routine({"meta": {}})

    def test_legacy_history_is_allowed_only_when_policy_is_undeclared(self):
        doc = {"meta": {}, "results": []}
        self.assertIs(require_routine_if_declared(doc), doc)
        with self.assertRaises(ValueError):
            require_routine_if_declared({"meta": {"timing_reps": 1}})

    def test_zopfli_has_a_separate_single_rep_contract(self):
        doc = zopfli_doc()
        self.assertIs(require_frozen_zopfli(doc), doc)
        for bad in (None, 5, "1", 1.0, True):
            with self.subTest(reps=bad), self.assertRaises(ValueError):
                require_frozen_zopfli(zopfli_doc(reps=bad))
        with self.assertRaises(ValueError):
            require_frozen_zopfli(zopfli_doc(frozen=False))
        with self.assertRaises(ValueError):
            require_frozen_zopfli(zopfli_doc(aggregation="median"))

    def test_committed_artifacts_declare_their_protocol(self):
        results = Path(__file__).resolve().parent / "results"
        load_routine(results / "latest.json")
        load_routine(results / "decode_density.json")
        load_frozen_zopfli(results / "zopfli-ceiling.json")


if __name__ == "__main__":
    unittest.main()
