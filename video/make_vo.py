#!/usr/bin/env python3
"""Generate per-cue scratch voice-over and timing data.

For each scene: one WAV per narration cue (espeak-ng), measured with ffprobe,
concatenated into <Scene>.wav, with <Scene>_cues.json recording each cue's
narration-relative start and duration. Scenes schedule beats against these via
CueScene.at_cue().

Usage (inside the nix shell, from the repo root):
    python3 video/make_vo.py [SceneA SceneB ...]     # default: all scenes
"""
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from narration import NARRATION  # noqa: E402

OUT = HERE / "out" / "audio"
RATE = "165"


def dur_of(path):
    r = subprocess.run(
        ["ffprobe", "-v", "error", "-show_entries", "format=duration",
         "-of", "csv=p=0", str(path)],
        capture_output=True, text=True, check=True)
    return float(r.stdout.strip())


def build_scene(scene):
    cues = NARRATION[scene]
    OUT.mkdir(parents=True, exist_ok=True)
    meta, wavs, t = [], [], 0.0
    for i, (key, text) in enumerate(cues):
        wav = OUT / f"{scene}_{i:02d}_{key}.wav"
        subprocess.run(
            ["espeak-ng", "-v", "en", "-s", RATE, "-w", str(wav), text],
            check=True)
        d = dur_of(wav)
        meta.append({"key": key, "start": round(t, 3), "dur": round(d, 3)})
        wavs.append(wav)
        t += d
    lst = OUT / f"{scene}_concat.txt"
    lst.write_text("".join(f"file '{w.name}'\n" for w in wavs))
    subprocess.run(
        ["ffmpeg", "-y", "-loglevel", "error", "-f", "concat", "-safe", "0",
         "-i", str(lst), "-c", "copy", str(OUT / f"{scene}.wav")],
        check=True)
    (OUT / f"{scene}_cues.json").write_text(json.dumps(meta, indent=1))
    print(f"{scene}: {len(cues)} cues, {t:.1f}s")
    return t


def main():
    targets = sys.argv[1:] or list(NARRATION)
    total = sum(build_scene(s) for s in targets)
    print(f"total narration: {total:.1f}s")


if __name__ == "__main__":
    main()
