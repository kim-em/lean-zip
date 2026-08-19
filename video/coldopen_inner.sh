#!/usr/bin/env bash
# Inner cold-open compositor; runs inside the nix shell provided by
# make_coldopen.sh (agg, ffmpeg, python3, fonts on PATH).
set -euo pipefail

for p in ${buildInputs:-}; do
  if ls "$p"/share/fonts/truetype/*.ttf >/dev/null 2>&1; then
    ln -sf "$p"/share/fonts/truetype/*.ttf video/.fonts/
  fi
done
export FONTCONFIG_FILE=$PWD/video/fonts.conf
INTER=video/.fonts/InterVariable.ttf
JBM=video/.fonts/JetBrainsMonoNL-Regular.ttf

python3 video/make_cast.py

for side in lean rust; do
  agg --font-family "JetBrains Mono NL" --font-size 22 --line-height 1.35 \
      --cols 46 --rows 6 \
      video/out/cast/$side.cast video/out/cast/$side.gif
  ffmpeg -y -loglevel error -i video/out/cast/$side.gif \
    -movflags faststart -pix_fmt yuv420p -r 30 video/out/cast/$side.mp4
done

read -r SHOW LT SM TOTAL < <(python3 - <<'PYEOF'
import json
cues = {c["key"]: c for c in
        json.load(open("video/out/audio/ColdOpenScene_cues.json"))}
total = max(c["start"] + c["dur"] for c in cues.values()) + 0.4
print(cues["show"]["start"], cues["less_time"]["start"],
      cues["smaller"]["start"], round(total, 2))
PYEOF
)
echo "cues: show=$SHOW less_time=$LT smaller=$SM total=$TOTAL"

TW=576
TY=250
LX=44
RX=660
LY=$((TY - 46))
END_TITLE=$(python3 -c "print($SM + 2.5)")
RULE1_Y=$((TY + 118))
RULE2_Y=$((TY + 80))

FILTER="\
[1:v]scale=$TW:-2[rt];\
[2:v]scale=$TW:-2[lt];\
[0:v][rt]overlay=$LX:$TY:enable='gte(t,$SHOW)'[a];\
[a][lt]overlay=$RX:$TY:enable='gte(t,$SHOW)'[b];\
[b]drawtext=fontfile=$INTER:text='Lean is faster than Rust?':fontsize=54:fontcolor=0xe6e8eb:x=(w-text_w)/2:y=(h-text_h)/2:enable='lt(t,$SHOW)',\
drawtext=fontfile=$INTER:text='miniz_oxide  (Rust)':fontsize=26:fontcolor=0x9aa3ad:x=$LX:y=$LY:enable='gte(t,$SHOW)',\
drawtext=fontfile=$INTER:text='lean-zip  (Lean)':fontsize=26:fontcolor=0x9aa3ad:x=$RX:y=$LY:enable='gte(t,$SHOW)',\
drawtext=fontfile=$INTER:text='bench/results/whole_tar_l6.json · chungus2 · median of 9':fontsize=17:fontcolor=0x5c6570:x=(w-text_w)/2:y=660:enable='gte(t,$SHOW)',\
drawbox=x=$((RX + 14)):y=$RULE1_Y:w=300:h=2:color=0x57b183@0.9:t=fill:enable='gte(t,$LT)',\
drawbox=x=$((RX + 14)):y=$RULE2_Y:w=300:h=2:color=0x57b183@0.9:t=fill:enable='gte(t,$SM)',\
drawtext=fontfile=$INTER:text='Why Lean is faster than Rust':fontsize=44:fontcolor=0xe6e8eb:x=(w-text_w)/2:y=90:enable='gte(t,$END_TITLE)'[v]"

ffmpeg -y -loglevel error \
  -f lavfi -i "color=c=0x0e1116:s=1280x720:d=$TOTAL:r=30" \
  -itsoffset "$SHOW" -i video/out/cast/rust.mp4 \
  -itsoffset "$SHOW" -i video/out/cast/lean.mp4 \
  -i video/out/audio/ColdOpenScene.wav \
  -filter_complex "$FILTER" \
  -map "[v]" -map 3:a -c:v libx264 -pix_fmt yuv420p -c:a aac \
  -t "$TOTAL" video/out/final/ColdOpenScene.mp4
echo "wrote video/out/final/ColdOpenScene.mp4"
