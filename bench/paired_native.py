#!/usr/bin/env python3
"""Cell-interleaved native benchmark comparison.

Run the ``bench-report --native-cell`` binaries from two worktrees immediately
next to each other for every corpus-file/level cell.  The checkerboard order
balances before-first and after-first cells while every row keeps the binary's
reported median-of-5 dashboard policy.  An atomic checkpoint records enough
provenance to resume without silently mixing binaries, sources, inputs, CPUs,
driver versions, or measurement protocols.

The caller owns scheduling isolation.  A review-grade Linux invocation is:

  coresched new -- taskset -c 95 python3 bench/paired_native.py \
    BEFORE_ROOT AFTER_ROOT /tmp/before.json /tmp/after.json \
    --manifest /tmp/paired-manifest.json --require-private-cookie
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shlex
import stat
import subprocess
import sys
import tempfile
import time


LEVELS = tuple(range(1, 11))
EXPECTED_TIMING_POLICY = {
    "timing_aggregation": "median",
    "timing_reps": 5,
}
ORDER_SCHEME = "checkerboard (file index + level index) parity"
PROTOCOL_VERSION = 3
LINK_FLAGS_WITH_ARGUMENT = {"-L", "--sysroot", "-Xlinker", "-mllvm"}


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_text(value: str) -> str:
    return sha256_bytes(value.encode("utf-8"))


def reject_duplicate_object_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    value: dict[str, object] = {}
    for key, item in pairs:
        if key in value:
            raise ValueError(f"duplicate JSON object key: {key}")
        value[key] = item
    return value


def strict_json_loads(value: str) -> object:
    return json.loads(
        value,
        object_pairs_hook=reject_duplicate_object_keys,
        parse_constant=lambda token: (_ for _ in ()).throw(
            ValueError(f"non-finite JSON constant: {token}")
        ),
    )


def normalized_response_tokens(path: Path, root: Path) -> list[str]:
    if not path.is_file():
        raise RuntimeError(f"missing benchmark response file: {path}")
    return [
        token.replace(str(root), "<ROOT>")
        for token in shlex.split(path.read_text(encoding="utf-8"))
    ]


def response_link_flags(path: Path, root: Path) -> list[str]:
    """Extract configuration flags while excluding root-local object inputs."""
    tokens = shlex.split(path.read_text(encoding="utf-8")) if path.is_file() else None
    if tokens is None:
        raise RuntimeError(f"missing benchmark response file: {path}")
    flags: list[str] = []
    pending: str | None = None
    for token in tokens:
        normalized = token.replace(str(root), "<ROOT>")
        if pending is not None:
            flags.append(normalized)
            pending = None
        elif token in LINK_FLAGS_WITH_ARGUMENT:
            flags.append(token)
            pending = token
        elif token.startswith("-"):
            flags.append(normalized)
    if pending is not None:
        raise RuntimeError(f"unterminated link flag {pending} in {path}")
    return flags


def git(root: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(root), *args], text=True
    ).strip()


def git_bytes(root: Path, *args: str) -> bytes:
    return subprocess.check_output(["git", "-C", str(root), *args])


def source_fingerprint(root: Path) -> dict[str, object]:
    """Fingerprint tracked changes and the bytes of every untracked path."""
    status_bytes = git_bytes(
        root, "status", "--porcelain=v1", "-z", "--untracked-files=all"
    )
    diff_bytes = git_bytes(root, "diff", "--binary", "HEAD", "--")
    untracked = git_bytes(
        root, "ls-files", "--others", "--exclude-standard", "-z"
    ).split(b"\0")
    untracked_digest = hashlib.sha256()
    for raw_name in sorted(name for name in untracked if name):
        path = root / os.fsdecode(raw_name)
        info = path.lstat()
        untracked_digest.update(len(raw_name).to_bytes(8, "big"))
        untracked_digest.update(raw_name)
        untracked_digest.update(info.st_mode.to_bytes(8, "big"))
        if stat.S_ISREG(info.st_mode):
            untracked_digest.update(bytes.fromhex(sha256_file(path)))
        elif stat.S_ISLNK(info.st_mode):
            untracked_digest.update(os.fsencode(os.readlink(path)))
    pieces = {
        "status_sha256": sha256_bytes(status_bytes),
        "diff_head_sha256": sha256_bytes(diff_bytes),
        "untracked_content_sha256": untracked_digest.hexdigest(),
    }
    return {
        **pieces,
        "fingerprint_sha256": sha256_text(
            json.dumps(pieces, sort_keys=True, separators=(",", ":"))
        ),
        "dirty": bool(status_bytes),
    }


def atomic_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp_name = tempfile.mkstemp(prefix=path.name + ".", dir=path.parent)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as stream:
            json.dump(value, stream, indent=2, sort_keys=False, allow_nan=False)
            stream.write("\n")
        os.replace(tmp_name, path)
    except BaseException:
        try:
            os.unlink(tmp_name)
        except FileNotFoundError:
            pass
        raise


def corpus_files(root: Path) -> dict[str, Path]:
    corpora = root / "bench" / "corpora"
    found: dict[str, Path] = {}
    for corpus in sorted(corpora.iterdir(), key=lambda path: path.name):
        if not corpus.is_dir():
            continue
        for path in sorted(corpus.iterdir(), key=lambda item: item.name):
            if path.is_file():
                found[f"{corpus.name}/{path.name}"] = path
    if not found:
        raise RuntimeError(f"no corpus files under {corpora}")
    return found


def private_cookie() -> str | None:
    try:
        output = subprocess.check_output(
            ["coresched", "get", "--source", str(os.getpid())],
            text=True,
            stderr=subprocess.STDOUT,
        )
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None
    match = re.search(r"0x[0-9a-fA-F]+", output)
    return match.group(0).lower() if match else None


def is_private_cookie(cookie: object) -> bool:
    return (
        isinstance(cookie, str)
        and re.fullmatch(r"0x[0-9a-f]+", cookie) is not None
        and int(cookie, 16) != 0
    )


def affinity() -> list[int] | None:
    try:
        return sorted(os.sched_getaffinity(0))
    except AttributeError:
        return None


def parse_timing_policy(value: object) -> dict[str, object]:
    if not isinstance(value, dict):
        raise RuntimeError("benchmark timing policy must be a JSON object")
    aggregation = value.get("timing_aggregation")
    repetitions = value.get("timing_reps")
    if not isinstance(aggregation, str) or type(repetitions) is not int:
        raise RuntimeError(f"invalid benchmark timing policy: {value!r}")
    policy = {
        "timing_aggregation": aggregation,
        "timing_reps": repetitions,
    }
    if policy != EXPECTED_TIMING_POLICY:
        raise RuntimeError(
            f"paired benchmarks require {EXPECTED_TIMING_POLICY}, got {policy}"
        )
    return policy


def binary_timing_policy(binary: Path, root: Path) -> dict[str, object]:
    # Query from an empty temporary CWD. A stale pre-protocol binary interprets
    # unknown arguments as an output filename; with no corpora here it fails the
    # JSON handshake quickly and cannot dirty either compared checkout.
    try:
        with tempfile.TemporaryDirectory(prefix="lean-zip-timing-policy.") as tmp:
            proc = subprocess.run(
                [str(binary), "--timing-policy"],
                cwd=tmp,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=10,
            )
    except subprocess.TimeoutExpired as error:
        raise RuntimeError(f"timing-policy query timed out for {binary}") from error
    if proc.returncode != 0:
        raise RuntimeError(
            f"could not query benchmark timing policy from {binary}:\n"
            f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        )
    try:
        value = strict_json_loads(proc.stdout)
    except (json.JSONDecodeError, ValueError) as error:
        raise RuntimeError(
            f"invalid timing-policy JSON from {binary}: {proc.stdout!r}"
        ) from error
    return parse_timing_policy(value)


def link_search_directories(root: Path, link_flags: list[str]) -> list[Path]:
    values: list[str] = []
    index = 0
    while index < len(link_flags):
        token = link_flags[index]
        if token == "-L" and index + 1 < len(link_flags):
            values.append(link_flags[index + 1])
            index += 2
            continue
        if token.startswith("-L") and len(token) > 2:
            values.append(token[2:])
        index += 1
    directories: list[Path] = []
    for value in values:
        if value == "<ROOT>":
            candidates = [root]
        elif value.startswith("<ROOT>/"):
            candidates = [root / value.removeprefix("<ROOT>/")]
        else:
            path = Path(value)
            candidates = [path] if path.is_absolute() else [root / "bench" / path, root / path]
        directory = next((path.resolve() for path in candidates if path.is_dir()), None)
        if directory is not None and directory not in directories:
            directories.append(directory)
    return directories


def resolve_linked_library(root: Path, link_flags: list[str], library: str) -> Path:
    names = (f"lib{library}.a", f"lib{library}.so", f"lib{library}.dylib")
    for directory in link_search_directories(root, link_flags):
        for name in names:
            candidate = directory / name
            if candidate.is_file():
                return candidate.resolve()
    raise RuntimeError(f"could not resolve linked library -l{library}")


def relevant_link_input_hashes(root: Path, link_flags: list[str]) -> dict[str, str]:
    relative_paths = {
        "harness_source": Path("bench/ZipBenchReport.lean"),
        "timing_policy_source": Path("bench/Bench/ReportTiming.lean"),
        "harness_object": Path("bench/.lake/build/ir/ZipBenchReport.c.o.export"),
        "timing_policy_object": Path(
            "bench/.lake/build/ir/Bench/ReportTiming.c.o.export"
        ),
        "miniz_oxide_ffi": Path("bench/.lake/build/lib/libminiz_oxide_ffi.a"),
        "libdeflate_ffi": Path("bench/.lake/build/lib/liblibdeflate_ffi.a"),
        "zopfli_ffi": Path("bench/.lake/build/lib/libzopfli_ffi.a"),
    }
    missing = [str(root / path) for path in relative_paths.values() if not (root / path).is_file()]
    if missing:
        raise RuntimeError(f"missing relevant benchmark link inputs: {missing}")
    hashes = {name: sha256_file(root / path) for name, path in relative_paths.items()}
    if "-lminiz_oxide_shim" in link_flags:
        hashes["miniz_oxide_shim"] = sha256_file(
            resolve_linked_library(root, link_flags, "miniz_oxide_shim")
        )
    return hashes


def branch_info(root: Path) -> dict[str, object]:
    binary = root / "bench" / ".lake" / "build" / "bin" / "bench-report"
    response = binary.with_suffix(".rsp")
    if not binary.is_file():
        raise RuntimeError(f"missing benchmark binary: {binary}")
    link_flags = response_link_flags(response, root)
    response_tokens = normalized_response_tokens(response, root)
    link_inputs = relevant_link_input_hashes(root, link_flags)
    controlled_link_layout = {
        "link_flags": link_flags,
        "relevant_input_names": sorted(link_inputs),
    }
    timing_policy = binary_timing_policy(binary, root)
    source = source_fingerprint(root)
    comparator_names = ("miniz_oxide_ffi", "libdeflate_ffi", "zopfli_ffi")
    return {
        "root": str(root),
        "commit": git(root, "rev-parse", "HEAD"),
        "commit_short": git(root, "rev-parse", "--short", "HEAD"),
        "toolchain": (root / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "binary": str(binary),
        "binary_sha256": sha256_file(binary),
        "timing_policy": timing_policy,
        "harness_sha256": link_inputs["harness_source"],
        "link_flags": link_flags,
        "link_flags_sha256": sha256_text(
            json.dumps(link_flags, separators=(",", ":"))
        ),
        "link_response_layout_sha256": sha256_text(
            json.dumps(response_tokens, separators=(",", ":"))
        ),
        "controlled_link_layout_sha256": sha256_text(
            json.dumps(controlled_link_layout, sort_keys=True, separators=(",", ":"))
        ),
        "relevant_link_inputs_sha256": link_inputs,
        "comparator_archives_sha256": {
            name.removesuffix("_ffi"): link_inputs[name]
            for name in comparator_names
        },
        "actual_miniz_oxide_shim_sha256": link_inputs.get("miniz_oxide_shim"),
        "source_fingerprint": source,
        "dirty": source["dirty"],
    }


def finite_number(value: object) -> bool:
    return type(value) in (int, float) and math.isfinite(value)


def validate_row(
    row: object, pattern: str, level: int, expected_size: int
) -> dict[str, object]:
    if not isinstance(row, dict):
        raise RuntimeError(f"native-cell row must be an object: {row!r}")
    expected_key = ("native", pattern, level)
    actual_key = (row.get("compressor"), row.get("pattern"), row.get("level"))
    if actual_key != expected_key or type(row.get("level")) is not int:
        raise RuntimeError(
            f"native-cell key mismatch: expected {expected_key}, got {actual_key}"
        )
    if type(row.get("size")) is not int or row["size"] != expected_size:
        raise RuntimeError(
            f"native-cell size mismatch for {pattern} L{level}: "
            f"expected {expected_size}, got {row.get('size')!r}"
        )
    out_size = row.get("out_size")
    if type(out_size) is not int or out_size < 0:
        raise RuntimeError(f"invalid output size for {pattern} L{level}: {out_size!r}")
    ratio = row.get("ratio")
    exact_ratio = out_size / max(expected_size, 1)
    if not finite_number(ratio) or ratio < 0 or abs(ratio - exact_ratio) > 0.000051:
        raise RuntimeError(
            f"invalid ratio for {pattern} L{level}: {ratio!r} "
            f"(out_size={out_size}, size={expected_size})"
        )
    compress = row.get("compress_mbps")
    if not finite_number(compress) or compress <= 0:
        raise RuntimeError(
            f"invalid compression timing for {pattern} L{level}: {compress!r}"
        )
    decompress = row.get("decompress_mbps")
    if level <= 9:
        if not finite_number(decompress) or decompress <= 0:
            raise RuntimeError(
                f"invalid decompression timing for {pattern} L{level}: {decompress!r}"
            )
    elif decompress is not None:
        raise RuntimeError(
            f"level {level} decompression timing must be null, got {decompress!r}"
        )
    return row


def run_cell(
    info: dict[str, object], pattern: str, level: int, expected_size: int
) -> dict[str, object]:
    proc = subprocess.run(
        [str(info["binary"]), "--native-cell", pattern, str(level)],
        cwd=str(info["root"]),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"native cell failed ({info['commit_short']} {pattern} L{level}):\n"
            f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        )
    try:
        row = strict_json_loads(proc.stdout)
    except (json.JSONDecodeError, ValueError) as error:
        raise RuntimeError(
            f"invalid native-cell JSON ({pattern} L{level}): {proc.stdout!r}"
        ) from error
    return validate_row(row, pattern, level, expected_size)


def parse_levels(csv: str) -> tuple[int, ...]:
    parts = csv.split(",")
    if not parts or any(not part.strip() for part in parts):
        raise RuntimeError("levels must be a nonempty comma-separated list")
    tokens = [part.strip() for part in parts]
    if any(re.fullmatch(r"[0-9]+", token) is None for token in tokens):
        raise RuntimeError(f"invalid level list: {csv!r}")
    levels = tuple(int(token) for token in tokens)
    if any(level not in LEVELS for level in levels):
        raise RuntimeError(f"levels must be within {LEVELS}: {levels}")
    if len(set(levels)) != len(levels):
        raise RuntimeError(f"levels must be unique: {levels}")
    return levels


def planned_cells(
    patterns: list[str], levels: tuple[int, ...]
) -> list[tuple[str, int, tuple[str, str]]]:
    return [
        (
            pattern,
            level,
            ("before", "after")
            if (file_index + level_index) % 2 == 0
            else ("after", "before"),
        )
        for file_index, pattern in enumerate(patterns)
        for level_index, level in enumerate(levels)
    ]


def is_within(path: Path, root: Path) -> bool:
    return path == root or root in path.parents


def validate_paths(
    before_root: Path,
    after_root: Path,
    before_out: Path,
    after_out: Path,
    manifest: Path,
) -> None:
    if before_root == after_root:
        raise RuntimeError("before and after roots must be distinct")
    outputs = (before_out, after_out, manifest)
    if len(set(outputs)) != len(outputs):
        raise RuntimeError("before output, after output, and manifest must be distinct")
    for output in outputs:
        for root in (before_root, after_root):
            if is_within(output, root):
                raise RuntimeError(
                    f"benchmark outputs and manifest must be outside both roots: {output}"
                )


def validate_session(
    session: object, index: int, private_required: bool, total: int
) -> None:
    required = {
        "id",
        "started",
        "finished",
        "core_scheduling_cookie",
        "completed_cells_at_start",
        "completed_cells_at_end",
    }
    if not isinstance(session, dict) or required - set(session):
        raise RuntimeError(f"checkpoint session {index} is missing required fields")
    if session.get("id") != index:
        raise RuntimeError(f"invalid checkpoint session {index}")
    if not isinstance(session.get("started"), str):
        raise RuntimeError(f"checkpoint session {index} has no start timestamp")
    finished = session.get("finished")
    if finished is not None and not isinstance(finished, str):
        raise RuntimeError(f"checkpoint session {index} has invalid finish timestamp")
    interrupted = session.get("interrupted_before")
    if interrupted is not None and not isinstance(interrupted, str):
        raise RuntimeError(f"checkpoint session {index} has invalid interruption timestamp")
    cookie = session.get("core_scheduling_cookie")
    if cookie is not None and (
        not isinstance(cookie, str)
        or re.fullmatch(r"0x[0-9a-f]+", cookie) is None
    ):
        raise RuntimeError(f"checkpoint session {index} has invalid core cookie")
    if private_required and not is_private_cookie(cookie):
        raise RuntimeError(f"checkpoint session {index} lacks a private core cookie")
    started_count = session.get("completed_cells_at_start")
    if type(started_count) is not int or not 0 <= started_count <= total:
        raise RuntimeError(f"checkpoint session {index} has invalid starting count")
    ended_count = session.get("completed_cells_at_end")
    if ended_count is not None and (
        type(ended_count) is not int or not 0 <= ended_count <= total
    ):
        raise RuntimeError(f"checkpoint session {index} has invalid ending count")
    if finished is None and ended_count is not None:
        raise RuntimeError(f"unfinished checkpoint session {index} has an ending count")
    if finished is not None and ended_count is None:
        raise RuntimeError(f"finished checkpoint session {index} lacks an ending count")
    if ended_count is not None and ended_count < started_count:
        raise RuntimeError(f"checkpoint session {index} ending count moved backwards")


def validate_checkpoint(
    state: object,
    identity: dict[str, object],
    keys: list[tuple[str, int, tuple[str, str]]],
    input_sizes: dict[str, int],
) -> dict[str, object]:
    if not isinstance(state, dict):
        raise RuntimeError("checkpoint must be a JSON object")
    for key, value in identity.items():
        if state.get(key) != value:
            raise RuntimeError(f"checkpoint identity mismatch for {key}")
    if not isinstance(state.get("started"), str):
        raise RuntimeError("checkpoint has no start timestamp")
    sessions = state.get("sessions")
    cells = state.get("cells")
    pending_reruns = state.get("pending_rerun_cells")
    rerun_history = state.get("rerun_history")
    if (
        not isinstance(sessions, list)
        or not isinstance(cells, dict)
        or not isinstance(pending_reruns, list)
        or not isinstance(rerun_history, list)
    ):
        raise RuntimeError("checkpoint sessions/cells/reruns are malformed")
    valid = {f"{pattern}|{level}": (pattern, level, order) for pattern, level, order in keys}
    if (
        any(not isinstance(key, str) or key not in valid for key in pending_reruns)
        or len(set(pending_reruns)) != len(pending_reruns)
    ):
        raise RuntimeError("checkpoint pending rerun cells are invalid")
    unknown = set(cells) - set(valid)
    if unknown:
        raise RuntimeError(f"checkpoint contains unknown cells: {sorted(unknown)}")
    private_required = identity["private_cookie_required"]
    for index, session in enumerate(sessions):
        validate_session(session, index, private_required, len(keys))
    for entry in rerun_history:
        if not isinstance(entry, dict):
            raise RuntimeError("checkpoint rerun history is malformed")
        rerun_cells = entry.get("cells")
        cell_sessions = entry.get("cell_sessions")
        if (
            not isinstance(rerun_cells, list)
            or not rerun_cells
            or len(set(rerun_cells)) != len(rerun_cells)
            or any(not isinstance(key, str) or key not in valid for key in rerun_cells)
            or not isinstance(cell_sessions, dict)
            or set(cell_sessions) != set(rerun_cells)
            or any(
                type(session_index) is not int
                or not 0 <= session_index < len(sessions)
                for session_index in cell_sessions.values()
            )
            or not isinstance(entry.get("completed"), str)
        ):
            raise RuntimeError("checkpoint rerun history entry is invalid")
    for key, cell in cells.items():
        pattern, level, order = valid[key]
        if not isinstance(cell, dict) or cell.get("order") != list(order):
            raise RuntimeError(f"checkpoint order mismatch for {key}")
        elapsed = cell.get("elapsed_seconds")
        if not finite_number(elapsed) or elapsed < 0:
            raise RuntimeError(f"checkpoint elapsed time is invalid for {key}")
        session_index = cell.get("session")
        if type(session_index) is not int or not 0 <= session_index < len(sessions):
            raise RuntimeError(f"checkpoint session reference is invalid for {key}")
        validate_row(cell.get("before"), pattern, level, input_sizes[pattern])
        validate_row(cell.get("after"), pattern, level, input_sizes[pattern])
    if "finished" not in state:
        raise RuntimeError("checkpoint has no finish state")
    finished = state["finished"]
    if finished is not None and not isinstance(finished, str):
        raise RuntimeError("checkpoint finish timestamp is invalid")
    if finished is not None and len(cells) != len(keys):
        raise RuntimeError("checkpoint is marked finished but has missing cells")
    if finished is not None and pending_reruns:
        raise RuntimeError("checkpoint is marked finished with pending reruns")
    if finished is not None and not sessions:
        raise RuntimeError("finished checkpoint has no measurement sessions")
    if finished is not None:
        last_finished = sessions[-1].get("finished")
        if last_finished is None and sessions[-1].get("interrupted_before") is None:
            raise RuntimeError("finished checkpoint has an unaccounted open session")
        if last_finished is not None and last_finished != finished:
            raise RuntimeError("checkpoint finish state disagrees with its final session")
    return state


def load_checkpoint(path: Path) -> object:
    try:
        return strict_json_loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError, ValueError) as error:
        raise RuntimeError(f"invalid checkpoint JSON in {path}: {error}") from error


def begin_session(
    state: dict[str, object], cookie: str | None, now: str
) -> int:
    sessions = state["sessions"]
    assert isinstance(sessions, list)
    for session in sessions:
        if session["finished"] is None and "interrupted_before" not in session:
            session["interrupted_before"] = now
    session_index = len(sessions)
    cells = state["cells"]
    assert isinstance(cells, dict)
    sessions.append(
        {
            "id": session_index,
            "started": now,
            "finished": None,
            "core_scheduling_cookie": cookie,
            "completed_cells_at_start": len(cells),
            "completed_cells_at_end": None,
        }
    )
    state["finished"] = None
    return session_index


def prepare_reruns(
    state: dict[str, object], requested: list[str], valid_keys: set[str]
) -> None:
    """Persist one-shot rerun intent without re-deleting it after interruption."""
    cells = state["cells"]
    pending = state["pending_rerun_cells"]
    assert isinstance(cells, dict) and isinstance(pending, list)
    unknown = set(requested) - valid_keys
    if unknown:
        raise RuntimeError(f"unknown --rerun-cell keys: {sorted(unknown)}")
    new_requests = [key for key in requested if key not in pending]
    missing = [key for key in new_requests if key not in cells]
    if missing:
        raise RuntimeError(f"--rerun-cell entries are not in the checkpoint: {missing}")
    for key in new_requests:
        del cells[key]
        pending.append(key)
    if new_requests:
        state["finished"] = None


def complete_reruns(state: dict[str, object], finished: str) -> None:
    pending = state["pending_rerun_cells"]
    history = state["rerun_history"]
    cells = state["cells"]
    assert isinstance(pending, list) and isinstance(history, list) and isinstance(cells, dict)
    if pending:
        history.append(
            {
                "cells": list(pending),
                "completed": finished,
                "cell_sessions": {
                    key: cells[key]["session"] for key in pending
                },
            }
        )
        pending.clear()


def finalize_without_measurement(state: dict[str, object], finished: str) -> bool:
    """Finalize a complete interrupted checkpoint; leave finished state stable."""
    if state["finished"] is not None:
        return False
    sessions = state["sessions"]
    assert isinstance(sessions, list)
    for session in sessions:
        if session["finished"] is None and "interrupted_before" not in session:
            session["interrupted_before"] = finished
    complete_reruns(state, finished)
    state["finished"] = finished
    return True


def output_document(
    info: dict[str, object], rows: list[dict[str, object]], state: dict[str, object]
) -> dict[str, object]:
    policy = state["timing_policy"]
    assert isinstance(policy, dict)
    sessions = state["sessions"]
    assert isinstance(sessions, list)
    return {
        "meta": {
            "date": state["finished"],
            "machine": state["machine"],
            "git_commit": info["commit_short"],
            "toolchain": info["toolchain"],
            "timing_aggregation": policy["timing_aggregation"],
            "timing_reps": policy["timing_reps"],
            "pairing": "cell-interleaved checkerboard AB/BA",
            "order_scheme": ORDER_SCHEME,
            "cpu_affinity": state["cpu_affinity"],
            "core_scheduling_cookies": [
                session["core_scheduling_cookie"] for session in sessions
            ],
            "benchmark_sessions": len(sessions),
            "benchmark_binary_sha256": info["binary_sha256"],
            "benchmark_harness_sha256": info["harness_sha256"],
            "benchmark_driver_sha256": state["driver_sha256"],
            "source_fingerprint": info["source_fingerprint"],
            "link_flags_sha256": info["link_flags_sha256"],
            "link_response_layout_sha256": info["link_response_layout_sha256"],
            "controlled_link_layout_sha256": info["controlled_link_layout_sha256"],
            "relevant_link_inputs_sha256": info["relevant_link_inputs_sha256"],
            "note": (
                "compress_mbps/decompress_mbps are median-of-5 per cell; "
                "before/after cells ran adjacently in checkerboard order; "
                "ratio is deterministic"
            ),
        },
        "results": rows,
    }


def write_output_documents(
    before: dict[str, object],
    after: dict[str, object],
    keys: list[tuple[str, int, tuple[str, str]]],
    state: dict[str, object],
    before_out: Path,
    after_out: Path,
) -> None:
    sorted_keys = sorted((pattern, level) for pattern, level, _order in keys)
    cells = state["cells"]
    assert isinstance(cells, dict)
    before_rows = [
        cells[f"{pattern}|{level}"]["before"] for pattern, level in sorted_keys
    ]
    after_rows = [
        cells[f"{pattern}|{level}"]["after"] for pattern, level in sorted_keys
    ]
    atomic_json(before_out, output_document(before, before_rows, state))
    atomic_json(after_out, output_document(after, after_rows, state))
    print(f"wrote {len(before_rows)} paired rows -> {before_out}", file=sys.stderr)
    print(f"wrote {len(after_rows)} paired rows -> {after_out}", file=sys.stderr)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("before_root", type=Path)
    parser.add_argument("after_root", type=Path)
    parser.add_argument("before_out", type=Path)
    parser.add_argument("after_out", type=Path)
    parser.add_argument(
        "--manifest",
        type=Path,
        help="checkpoint/provenance path (default: AFTER_OUT.paired-manifest.json)",
    )
    parser.add_argument(
        "--levels",
        default=",".join(map(str, LEVELS)),
        help="comma-separated unique level subset (default: 1..10)",
    )
    parser.add_argument("--require-private-cookie", action="store_true")
    parser.add_argument(
        "--rerun-cell",
        action="append",
        default=[],
        metavar="CORPUS/FILE|LEVEL",
        help="discard and remeasure one completed checkpoint cell",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    before_root = args.before_root.resolve()
    after_root = args.after_root.resolve()
    before_out = args.before_out.resolve()
    after_out = args.after_out.resolve()
    manifest = (
        args.manifest.resolve()
        if args.manifest
        else after_out.with_name(after_out.stem + ".paired-manifest.json")
    )
    validate_paths(before_root, after_root, before_out, after_out, manifest)
    levels = parse_levels(args.levels)
    if len(set(args.rerun_cell)) != len(args.rerun_cell):
        raise RuntimeError("--rerun-cell entries must be unique")

    cpus = affinity()
    if cpus is None or len(cpus) != 1:
        raise RuntimeError(f"paired benchmark must be pinned to one CPU, got {cpus}")
    cookie = private_cookie()
    if args.require_private_cookie and not is_private_cookie(cookie):
        raise RuntimeError(f"private core-scheduling cookie required, got {cookie}")

    before = branch_info(before_root)
    after = branch_info(after_root)
    if before["toolchain"] != after["toolchain"]:
        raise RuntimeError(
            f"toolchain mismatch: {before['toolchain']} vs {after['toolchain']}"
        )
    for field in (
        "timing_policy",
        "harness_sha256",
        "link_flags",
        "controlled_link_layout_sha256",
        "relevant_link_inputs_sha256",
    ):
        if before[field] != after[field]:
            raise RuntimeError(
                f"benchmark build mismatch for {field}: "
                f"{before[field]} vs {after[field]}"
            )

    before_files = corpus_files(before_root)
    after_files = corpus_files(after_root)
    if before_files.keys() != after_files.keys():
        raise RuntimeError("before/after corpus file sets differ")
    input_hashes: dict[str, str] = {}
    input_sizes: dict[str, int] = {}
    for pattern in before_files:
        before_hash = sha256_file(before_files[pattern])
        after_hash = sha256_file(after_files[pattern])
        if before_hash != after_hash:
            raise RuntimeError(f"before/after corpus bytes differ: {pattern}")
        before_size = before_files[pattern].stat().st_size
        after_size = after_files[pattern].stat().st_size
        if before_size != after_size:
            raise RuntimeError(f"before/after corpus sizes differ: {pattern}")
        input_hashes[pattern] = before_hash
        input_sizes[pattern] = before_size

    keys = planned_cells(list(before_files), levels)
    machine = subprocess.check_output(["uname", "-mns"], text=True).strip()
    driver_sha256 = sha256_file(Path(__file__).resolve())
    identity = {
        "protocol_version": PROTOCOL_VERSION,
        "driver_sha256": driver_sha256,
        "machine": machine,
        "cpu_affinity": cpus,
        "private_cookie_required": args.require_private_cookie,
        "levels": list(levels),
        "before": before,
        "after": after,
        "input_sha256": input_hashes,
        "input_size": input_sizes,
        "timing_policy": before["timing_policy"],
        "order_scheme": ORDER_SCHEME,
    }

    if manifest.exists():
        state = validate_checkpoint(
            load_checkpoint(manifest), identity, keys, input_sizes
        )
        print(
            f"resuming {len(state['cells'])} completed pairs from {manifest}",
            file=sys.stderr,
        )
    else:
        state = {
            **identity,
            "started": dt.datetime.now(dt.timezone.utc).isoformat(),
            "finished": None,
            "sessions": [],
            "cells": {},
            "pending_rerun_cells": [],
            "rerun_history": [],
        }

    valid_keys = {f"{pattern}|{level}" for pattern, level, _order in keys}
    prepare_reruns(state, args.rerun_cell, valid_keys)

    now = dt.datetime.now(dt.timezone.utc).isoformat()
    missing_keys = [
        f"{pattern}|{level}"
        for pattern, level, _order in keys
        if f"{pattern}|{level}" not in state["cells"]
    ]
    if not missing_keys:
        if finalize_without_measurement(state, now):
            validate_checkpoint(state, identity, keys, input_sizes)
            atomic_json(manifest, state)
        write_output_documents(before, after, keys, state, before_out, after_out)
        print(f"manifest -> {manifest}", file=sys.stderr)
        return 0

    session_index = begin_session(state, cookie, now)
    atomic_json(manifest, state)

    total = len(keys)
    for pattern, level, order in keys:
        key = f"{pattern}|{level}"
        if key in state["cells"]:
            continue
        cell_started = time.monotonic()
        measured: dict[str, dict[str, object]] = {}
        for role in order:
            info = before if role == "before" else after
            measured[role] = run_cell(info, pattern, level, input_sizes[pattern])
        state["cells"][key] = {
            "order": list(order),
            "session": session_index,
            "elapsed_seconds": round(time.monotonic() - cell_started, 3),
            "before": measured["before"],
            "after": measured["after"],
        }
        atomic_json(manifest, state)
        done = len(state["cells"])
        print(
            f"paired {done:3}/{total}: {pattern} L{level} ({order[0]} first)",
            file=sys.stderr,
            flush=True,
        )

    finished = dt.datetime.now(dt.timezone.utc).isoformat()
    state["sessions"][session_index]["finished"] = finished
    state["sessions"][session_index]["completed_cells_at_end"] = len(state["cells"])
    complete_reruns(state, finished)
    state["finished"] = finished
    validate_checkpoint(state, identity, keys, input_sizes)
    atomic_json(manifest, state)
    write_output_documents(before, after, keys, state, before_out, after_out)
    print(f"manifest -> {manifest}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f"paired_native: {error}", file=sys.stderr)
        raise SystemExit(1)
