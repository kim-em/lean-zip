"""Strict timing-protocol validators and loaders for benchmark JSON.

Routine dashboard documents and external comparator records are median-of-5.
The frozen zopfli ratio ceiling is the only single-repetition artifact, and it
has a separate loader so routine call sites cannot accidentally opt out of
validation.
"""

import json
from collections.abc import Mapping
from pathlib import Path


ROUTINE_AGGREGATION = "median"
ROUTINE_REPS = 5
ZOPFLI_AGGREGATION = "single"
ZOPFLI_REPS = 1


def require_routine_timing(values, source="timing metadata"):
    """Require flat machine-readable median-of-5 timing provenance.

    ``values`` may be a benchmark document's ``meta`` mapping or one JSON
    object emitted by an external comparator. Keeping this check at the
    mapping level gives producers and consumers one exact contract.
    """
    if not isinstance(values, Mapping):
        raise ValueError(f"{source}: expected a JSON object, got {type(values).__name__}")
    aggregation = values.get("timing_aggregation")
    reps = values.get("timing_reps")
    if aggregation != ROUTINE_AGGREGATION or type(reps) is not int or reps != ROUTINE_REPS:
        raise ValueError(
            f"{source}: expected timing_aggregation={ROUTINE_AGGREGATION!r} "
            f"and integer timing_reps={ROUTINE_REPS}; got "
            f"{aggregation!r} and {reps!r}"
        )
    return values


def require_routine(doc, source="benchmark document"):
    """Require exact machine-readable median-of-5 routine provenance."""
    meta = doc.get("meta", {})
    require_routine_timing(meta, f"{source}.meta")
    return doc


def require_routine_if_declared(doc, source="benchmark document"):
    """Validate new history frames while permitting pre-schema legacy frames."""
    meta = doc.get("meta", {})
    if "timing_aggregation" in meta or "timing_reps" in meta:
        require_routine(doc, source)
    return doc


def require_frozen_zopfli(doc, source="zopfli benchmark document"):
    """Require the explicit frozen, single-repetition zopfli artifact schema."""
    meta = doc.get("meta", {})
    aggregation = meta.get("timing_aggregation")
    reps = meta.get("timing_reps")
    if (meta.get("frozen") is not True
            or aggregation != ZOPFLI_AGGREGATION
            or type(reps) is not int
            or reps != ZOPFLI_REPS):
        raise ValueError(
            f"{source}: expected frozen zopfli metadata with "
            f"timing_aggregation={ZOPFLI_AGGREGATION!r} and integer "
            f"timing_reps={ZOPFLI_REPS}; got frozen={meta.get('frozen')!r}, "
            f"aggregation={aggregation!r}, reps={reps!r}"
        )
    return doc


def _load(path):
    path = Path(path)
    return json.loads(path.read_text()), path


def load_routine(path):
    doc, path = _load(path)
    return require_routine(doc, str(path))


def load_frozen_zopfli(path):
    doc, path = _load(path)
    return require_frozen_zopfli(doc, str(path))
