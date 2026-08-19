#!/usr/bin/env bash
# Composite the cold open: title card, two agg-rendered terminals side by
# side with identity labels OUTSIDE the panes, cue-timed against the scratch
# VO, ending on the video title. Produces video/out/final/ColdOpenScene.mp4.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p video/out/cast video/out/final video/.fonts
nix-shell -p asciinema-agg ffmpeg python3 inter jetbrains-mono fontconfig \
  --run "bash video/coldopen_inner.sh"
