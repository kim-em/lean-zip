import json
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

import decode_density
from comparators import run_external


def completed(stat):
    return SimpleNamespace(stdout=json.dumps(stat) + "\n")


class ExternalTimingContractTests(unittest.TestCase):
    def collect_normal(self, stat):
        comparator = {"fixture": ("fixture", ["fixture-bin"], range(1, 2))}
        with (
            patch.dict(run_external.COMPARATORS, comparator, clear=True),
            patch.object(run_external, "runnable", return_value=True),
            patch.object(run_external.subprocess, "run", return_value=completed(stat)),
        ):
            return run_external.collect(
                "fixture", [(Path("unused.bin"), "fixture-pattern", 10)])

    def collect_decode(self, stat):
        comparator = {"fixture": ("fixture", ["fixture-bin", "decode"])}
        with tempfile.TemporaryDirectory() as tmp:
            stream = Path(tmp) / "fixture.deflate"
            stream.write_bytes(b"compressed")
            with (
                patch.dict(decode_density.COMPARATORS, comparator, clear=True),
                patch.object(decode_density, "runnable", return_value=True),
                patch.object(decode_density.subprocess, "run", return_value=completed(stat)),
            ):
                return decode_density.collect(
                    "fixture", [(stream, "corpus", "corpus/file", 1)])

    def test_normal_driver_accepts_median_of_five(self):
        rows = self.collect_normal({
            "out_size": 5,
            "compress_mbps": 2.0,
            "decompress_mbps": 3.0,
            "timing_aggregation": "median",
            "timing_reps": 5,
        })
        self.assertEqual(len(rows), 1)

    def test_normal_driver_treats_timing_mismatch_as_fatal(self):
        with self.assertRaisesRegex(ValueError, "fixture-pattern"):
            self.collect_normal({
                "out_size": 5,
                "compress_mbps": 2.0,
                "decompress_mbps": 3.0,
                "timing_aggregation": "median",
                "timing_reps": 1,
            })

    def test_decode_driver_accepts_median_of_five(self):
        rows = self.collect_decode({
            "decompress_mbps": 3.0,
            "decoded_size": 10,
            "timing_aggregation": "median",
            "timing_reps": 5,
        })
        self.assertEqual(len(rows), 1)

    def test_decode_driver_treats_timing_mismatch_as_fatal(self):
        with self.assertRaisesRegex(ValueError, "corpus/file"):
            self.collect_decode({
                "decompress_mbps": 3.0,
                "decoded_size": 10,
                "timing_aggregation": "single",
                "timing_reps": 5,
            })


if __name__ == "__main__":
    unittest.main()
