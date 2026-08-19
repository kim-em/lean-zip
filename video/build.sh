#!/usr/bin/env bash
# End-to-end mockup build: data prep, per-cue scratch VO, manim render, mux,
# concat. Runs everything under nix-shell. Usage:
#   video/build.sh              # all scenes
#   video/build.sh Theorem      # scenes whose class name contains "Theorem"
# Env:
#   QUALITY=l|m|h               # 480p15 / 720p30 (default) / 1080p60
set -euo pipefail
cd "$(dirname "$0")/.."

FILTER="${1:-}"
Q="${QUALITY:-m}"
case "$Q" in
  m) QFLAG=-qm; RES=720p30 ;;
  h) QFLAG=-qh; RES=1080p60 ;;
  l) QFLAG=-ql; RES=480p15 ;;
  *) echo "QUALITY must be l, m, or h"; exit 1 ;;
esac

SCENES=$(python3 - "$FILTER" <<'EOF'
import sys
sys.path.insert(0, "video")
from narration import NARRATION
f = sys.argv[1] if len(sys.argv) > 1 else ""
print(" ".join(s for s in NARRATION if f.lower() in s.lower()))
EOF
)
[ -n "$SCENES" ] || { echo "no scenes match filter '$FILTER'"; exit 1; }
echo "building at $RES: $SCENES"

OUT=video/out
mkdir -p "$OUT/audio" "$OUT/final" video/.fonts

python3 video/prep_data.py

# split off the cold open: it is composited from terminal casts, not manim
MANIM_SCENES=""
COLD=""
for s in $SCENES; do
  if [ "$s" = "ColdOpenScene" ]; then COLD=1; else MANIM_SCENES="$MANIM_SCENES $s"; fi
done

nix-shell -p manim ffmpeg espeak-ng inter jetbrains-mono fontconfig --run "
set -euo pipefail
for p in \$buildInputs; do
  if ls \$p/share/fonts/truetype/*.ttf >/dev/null 2>&1; then
    ln -sf \$p/share/fonts/truetype/*.ttf video/.fonts/
  fi
done
export FONTCONFIG_FILE=\$PWD/video/fonts.conf
fc-list | grep -Ei 'inter|jetbrains' >/dev/null || {
  echo 'ERROR: fonts not visible to fontconfig'; exit 1; }

# 1) voice-over first: scenes read the cue timings during render
python3 video/make_vo.py $SCENES

# 2) render
if [ -n \"$MANIM_SCENES\" ]; then
  manim render $QFLAG --media_dir $OUT/media video/scenes.py $MANIM_SCENES
fi

# 3) mux each scene to the EXPLICIT narration duration (no silent freeze tail)
for scene in $MANIM_SCENES; do
  vid=\$(ls $OUT/media/videos/scenes/$RES/\$scene.mp4)
  adur=\$(ffprobe -v error -show_entries format=duration -of csv=p=0 $OUT/audio/\$scene.wav)
  total=\$(python3 -c \"print(float('\$adur') + 0.4)\")
  ffmpeg -y -loglevel error -i \"\$vid\" -i $OUT/audio/\$scene.wav \
    -filter_complex '[0:v]tpad=stop_mode=clone:stop_duration=10[v]' \
    -map '[v]' -map 1:a -c:v libx264 -pix_fmt yuv420p -c:a aac \
    -t \"\$total\" $OUT/final/\$scene.mp4
  echo \"muxed \$scene (\${total}s)\"
done
"

if [ -n "$COLD" ]; then
  video/make_coldopen.sh
fi

# concat EVERY rendered scene in narration.py order
nix-shell -p ffmpeg --run "
set -euo pipefail
ALL=\$(python3 -c \"
import sys; sys.path.insert(0, 'video')
from narration import NARRATION
print(' '.join(NARRATION))\")
: > $OUT/final/list.txt
for scene in \$ALL; do
  [ -f $OUT/final/\$scene.mp4 ] && echo \"file '\$scene.mp4'\" >> $OUT/final/list.txt
done
ffmpeg -y -loglevel error -f concat -safe 0 -i $OUT/final/list.txt \
  -c copy $OUT/mockup.mp4
echo 'wrote video/out/mockup.mp4 with:'; cat $OUT/final/list.txt
"
