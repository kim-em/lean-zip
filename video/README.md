# lean-zip video build

Manim project that renders the "Why Lean is faster than Rust" video from the
script in `video.md` (the merged deliverable, owned by the Codex session; the
`*-v1.md` / `*-v2.md` files are frozen historical drafts). This directory is
owned by the Claude session `claude-video-v1`.

## Layout

    narration.py    voice-over text per scene, the single source of truth for
                    the scratch VO; sync with video.md as it evolves
    prep_data.py    extracts the Pareto history + reference curves from git
                    into data/history.json (run from the repo root)
    scenes.py       manim scenes, one class per video scene
    build.sh        end-to-end mockup build: data prep, render, espeak-ng
                    scratch voice-over, mux, concat -> out/mockup.mp4

## Building

Everything runs under nix-shell (manim, ffmpeg, espeak-ng from nixpkgs):

    ./video/build.sh            # full mockup at low quality (-ql)
    ./video/build.sh Theorem    # single scene by class-name substring

The scratch voice-over is espeak-ng and deliberately robotic; Kim records the
real narration later. Scene durations follow the audio: the last video frame
is cloned out if the VO runs long, so timing reviews are honest about VO
length even before animations are fully paced.

## Status

- [x] TheoremScene (scene 2)
- [x] ParetoHistoryScene (scene 3, real dashboard data)
- [x] LazyMatchingScene (lazy chapter; the C panel shows the real accept
      condition vendored from libdeflate @ b122c8b into
      assets/libdeflate_lazy_accept.c, MIT-licensed with attribution)
- [ ] remaining scenes pending the merged video.md scene list
