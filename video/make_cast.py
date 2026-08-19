#!/usr/bin/env python3
"""Synthesize the two cold-open asciinema casts.

Numbers come from the committed nine-run medians in
bench/results/whole_tar_l6.json (video.md Scene 1 SB: one complete source,
never mixed). The typing cadence and the compressed wait are presentation;
the printed sizes and `real` times are the measurement.

Writes video/out/cast/{lean,rust}.cast (asciinema v2).
"""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
OUT = HERE / "out" / "cast"

COLS, ROWS = 46, 6
TYPE_S = 0.045          # per character
WAIT_S = 1.6            # compressed compute wait (the printed time is honest)

THEME = {
    "fg": "#e6e8eb", "bg": "#151a21",
    "palette": ":".join([
        "#2c3440", "#e35d6a", "#57b183", "#d9a441",
        "#5da9e9", "#a487d9", "#17becf", "#e6e8eb",
        "#5c6570", "#e35d6a", "#57b183", "#d9a441",
        "#5da9e9", "#a487d9", "#17becf", "#ffffff",
    ]),
}


def cast(cmd, size, wall_ms):
    events, t = [], 0.4
    prompt = "\x1b[38;5;2m$\x1b[0m "
    events.append([0.0, "o", prompt])
    for ch in cmd:
        events.append([round(t, 3), "o", ch])
        t += TYPE_S
    t += 0.3
    events.append([round(t, 3), "o", "\r\n"])
    t += WAIT_S
    events.append([round(t, 3), "o", f"{size}\r\n"])
    t += 0.15
    m, s = divmod(wall_ms / 1000.0, 60)
    events.append([round(t, 3), "o",
                   f"\r\nreal\t{int(m)}m{s:.3f}s\r\n"])
    t += 0.3
    header = {"version": 2, "width": COLS, "height": ROWS,
              "timestamp": 0, "theme": THEME}
    return "\n".join([json.dumps(header)] +
                     [json.dumps(e) for e in events]) + "\n"


def main():
    wt = json.loads(
        (HERE.parent / "bench" / "results" / "whole_tar_l6.json").read_text())
    e2e = wt["end_to_end"]
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "lean.cast").write_text(cast(
        "time deflate-lean silesia.tar",
        e2e["lean"]["size"], e2e["lean"]["wall_ms_median"]))
    (OUT / "rust.cast").write_text(cast(
        "time deflate-rust silesia.tar",
        e2e["rust"]["size"], e2e["rust"]["wall_ms_median"]))
    print("wrote lean.cast, rust.cast")


if __name__ == "__main__":
    main()
