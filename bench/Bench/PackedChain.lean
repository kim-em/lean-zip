import Zip
/-! # Packed `ByteArray` uint32 chain-table spike (issue #2779)

Measurement-first prototype for issue #2779: back the DEFLATE chain tables with a
raw `ByteArray` of little-endian uint32 entries (4 unboxed bytes/slot) instead of
the production merged `Array Nat` (8-byte tagged slots), to test whether the
smaller footprint buys L2 cache residency for the memory-bound chain walk at the
deep levels (L6–L8).

**This is distinct from the retired `Array UInt32` attempt (#2490/#2607).** That
experiment changed the *element type* — but an `Array UInt32` in Lean is still an
array of boxed `lean_object*` tagged scalars (same 8-byte slots), so it measured
slower with no cache benefit. The lever here is the *packing*: `ugetUInt32LE` /
`usetUInt32LE` read/write genuinely-unboxed 4-byte slots of a `ByteArray`.

To isolate the single variable (storage layout) this module builds two matchers
that are byte-for-byte identical except for the chain state:

* `arrMergedMatcher` — merged `Array Nat`, `[i]!` / `set!` access.
* `packedMergedMatcher` — merged packed `ByteArray`, `ugetUInt32LE` /
  `usetUInt32LE` behind a single (always-true, well-predicted) size guard.

Both carry a plain `Nat` accumulator and mirror the *lazy* merged loop
(`lz77ChainLazyIterPMerged`), which is the production matcher for every level
≥ 4 (so L6/L7/L8). Neither reproduces the production `USize`-accumulator
de-boxing (`chainWalkPackedU`), so their absolute ms is a little above production
`lzMatchP`; the A/B *delta between the two of them* is the packing signal the
issue asks for, and `lzMatchP` is reported alongside for absolute context.

These are `partial def`s living only in the dev-only bench package — no proof
obligations, nothing on a shipped path. If the packing pays here, the follow-up
threads the bounds lemmas into a real library variant (issue plan step 2).

The chain arrays hold absolute positions, sentinel `data.size` (≥ every real
position, so an unset link fails the `cand < pos` guard). The packed slot is a
uint32, so this prototype is valid for inputs `< 4 GiB`; the whole Silesia /
Canterbury bench corpus is far below that.
-/

namespace Bench.PackedChain

open Zip.Native.Deflate

/-! ### Packed `ByteArray` chain-table accessors -/

/-- Read chain-slot `i` (a stored absolute position) from the packed
    little-endian uint32 buffer. The size guard is always true for the fixed
    `4·(prevSize+hashSize)`-byte buffer and predicts not-taken, so it is off the
    memory-latency critical path; a real library variant discharges it with the
    same bounds lemma the production `Array` walk carries. -/
@[inline] def bget (c : ByteArray) (i : Nat) : Nat :=
  let off : USize := i.toUSize <<< 2
  if h : off.toNat + 4 ≤ c.size then (c.ugetUInt32LE off h).toNat else 0

/-- Write absolute position `v` into chain-slot `i` of the packed buffer as one
    little-endian uint32 (in place when `c` is exclusive, which it is on the
    linearly-threaded hot path). -/
@[inline] def bset (c : ByteArray) (i : Nat) (v : Nat) : ByteArray :=
  let off : USize := i.toUSize <<< 2
  if h : off.toNat + 4 ≤ c.size then c.usetUInt32LE off v.toUInt32 h else c

/-- Fill a fresh packed buffer of `slots` uint32 entries with the sentinel
    `sentinel` (LE). One-time per matcher run, off the hot loop. -/
def mkSentinelBuf (slots sentinel : Nat) : ByteArray := Id.run do
  let s := sentinel.toUInt32
  let b0 := s.toUInt8
  let b1 := (s >>> 8).toUInt8
  let b2 := (s >>> 16).toUInt8
  let b3 := (s >>> 24).toUInt8
  let mut c := ByteArray.emptyWithCapacity (4 * slots)
  for _ in [0:slots] do
    c := ((c.push b0).push b1 |>.push b2).push b3
  return c

/-! ### Packed chain walk / insertion / lazy loop (mirror of the merged path) -/

/-- Packed-buffer copy of `chainWalkPacked` (Nat accumulator, `scan_end`
    prefilter). Identical control flow; the only change is the chain link read
    `bget cbuf (cand &&& 0x7FFF)` in place of `prev[cand &&& 0x7FFF]`. Result is
    packed as `bestPos * 512 + bestLen`. -/
partial def chainWalkBA (data cbuf : ByteArray) (windowSize pos maxLen niceLen : Nat)
    (hpm : pos + maxLen ≤ data.size) (cand fuel bestLen bestPos : Nat) : Nat :=
  if fuel = 0 then bestPos * 512 + bestLen
  else if hc : cand < pos ∧ pos - cand ≤ windowSize then
    have hcand : cand + maxLen ≤ data.size := by omega
    let skip : Bool := if hbl : bestLen < maxLen then
        data[cand + bestLen]'(by omega) != data[pos + bestLen]'(by omega)
      else false
    if skip then
      if bestLen ≥ min niceLen maxLen then bestPos * 512 + bestLen
      else chainWalkBA data cbuf windowSize pos maxLen niceLen hpm
        (bget cbuf (cand &&& 0x7FFF)) (fuel - 1) bestLen bestPos
    else
      let ml := lz77Greedy.countMatch data cand pos maxLen hcand hpm
      let bl := if ml > bestLen then ml else bestLen
      let bp := if ml > bestLen then cand else bestPos
      if bl ≥ min niceLen maxLen then bp * 512 + bl
      else chainWalkBA data cbuf windowSize pos maxLen niceLen hpm
        (bget cbuf (cand &&& 0x7FFF)) (fuel - 1) bl bp
  else bestPos * 512 + bestLen

/-- Packed-buffer copy of `updateHashesMerged`: insert positions
    `pos+1 .. pos+min(matchLen-1, insertCap)` into the merged packed buffer. -/
partial def updateHashesBA (data cbuf : ByteArray) (hashSize prevSize pos j matchLen insertCap : Nat) : ByteArray :=
  if j < matchLen ∧ j ≤ insertCap then
    if h : pos + j + 2 < data.size then
      let hsh := lz77Greedy.hash3 data (pos + j) hashSize h
      let head := bget cbuf (prevSize + hsh)
      let cbuf := bset (bset cbuf (prevSize + hsh) (pos + j)) ((pos + j) &&& 0x7FFF) head
      updateHashesBA data cbuf hashSize prevSize pos (j + 1) matchLen insertCap
    else
      updateHashesBA data cbuf hashSize prevSize pos (j + 1) matchLen insertCap
  else cbuf

/-- Packed-buffer copy of `lz77LazyMergedLoop`: the lazy one-byte-lookahead
    merged matcher, chain state a packed `ByteArray`. -/
partial def lazyLoopBA (data cbuf : ByteArray)
    (windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth pos : Nat)
    (acc : Array UInt32) : Array UInt32 :=
  if hlt : pos + 2 < data.size then
    let h := lz77Greedy.hash3 data pos hashSize hlt
    let head := bget cbuf (prevSize + h)
    let cbuf := bset cbuf (prevSize + h) pos
    let cbuf := bset cbuf (pos &&& 0x7FFF) head
    let maxLen := min 258 (data.size - pos)
    have hmaxLenP : pos + maxLen ≤ data.size := by omega
    let r := chainWalkBA data cbuf windowSize pos maxLen niceLen hmaxLenP head maxChain 0 0
    let matchLen := r % 512
    let matchPos := r / 512
    if matchLen ≥ 3 then
      if pos + matchLen ≤ data.size then
        if h3lt : pos + 3 < data.size then
          if matchLen < goodMatch then
            let h2 := lz77Greedy.hash3 data (pos + 1) hashSize (by omega)
            let head2 := bget cbuf (prevSize + h2)
            let maxLen2 := min 258 (data.size - (pos + 1))
            have hmaxLen2P : (pos + 1) + maxLen2 ≤ data.size := by omega
            let r2 := chainWalkBA data cbuf windowSize (pos + 1) maxLen2 niceLen hmaxLen2P head2 lazyDepth 0 0
            let matchLen2 := r2 % 512
            let matchPos2 := r2 / 512
            if lazyAcceptCost matchLen (pos - matchPos) matchLen2 (pos + 1 - matchPos2) then
              if pos + 1 + matchLen2 ≤ data.size then
                let cbuf := updateHashesBA data cbuf hashSize prevSize pos 1 (matchLen2 + 1) insertCap
                lazyLoopBA data cbuf windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth (pos + 1 + matchLen2)
                  (acc.push (packTok (.literal (data[pos]'(by omega)))) |>.push
                    (packTok (.reference matchLen2 (pos + 1 - matchPos2))))
              else
                let cbuf := updateHashesBA data cbuf hashSize prevSize pos 1 matchLen insertCap
                lazyLoopBA data cbuf windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth (pos + matchLen)
                  (acc.push (packTok (.reference matchLen (pos - matchPos))))
            else
              let cbuf := updateHashesBA data cbuf hashSize prevSize pos 1 matchLen insertCap
              lazyLoopBA data cbuf windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth (pos + matchLen)
                (acc.push (packTok (.reference matchLen (pos - matchPos))))
          else
            let cbuf := updateHashesBA data cbuf hashSize prevSize pos 1 matchLen insertCap
            lazyLoopBA data cbuf windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth (pos + matchLen)
              (acc.push (packTok (.reference matchLen (pos - matchPos))))
        else
          lazyLoopBA data cbuf windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth (pos + matchLen)
            (acc.push (packTok (.reference matchLen (pos - matchPos))))
      else
        lazyLoopBA data cbuf windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth (pos + 1)
          (acc.push (packTok (.literal (data[pos]'(by omega)))))
    else
      lazyLoopBA data cbuf windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth (pos + 1)
        (acc.push (packTok (.literal (data[pos]'(by omega)))))
  else
    trailingP data pos acc

/-- Packed-`ByteArray` merged lazy matcher — the spike variant. -/
def packedMergedMatcher (data : ByteArray) (maxChain : Nat) (windowSize : Nat := 32768)
    (insertCap : Nat := 1000000000) (goodMatch : Nat := 259) (niceLen : Nat := 258)
    (lazyDepth : Nat := maxChain) : Array UInt32 :=
  if data.size < 3 then
    trailingP data 0 #[]
  else
    let hashSize := 65536
    let prevSize := min chainWinSize data.size
    let cbuf := mkSentinelBuf (prevSize + hashSize) data.size
    lazyLoopBA data cbuf windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth 0
      (Array.emptyWithCapacity data.size)

/-! ### `Array Nat` twin (the control) — identical code, `[i]!` / `set!` access -/

@[inline] def aget (c : Array Nat) (i : Nat) : Nat := c[i]!

@[inline] def aset (c : Array Nat) (i : Nat) (v : Nat) : Array Nat := c.set! i v

partial def chainWalkArr (data : ByteArray) (c : Array Nat) (windowSize pos maxLen niceLen : Nat)
    (hpm : pos + maxLen ≤ data.size) (cand fuel bestLen bestPos : Nat) : Nat :=
  if fuel = 0 then bestPos * 512 + bestLen
  else if hc : cand < pos ∧ pos - cand ≤ windowSize then
    have hcand : cand + maxLen ≤ data.size := by omega
    let skip : Bool := if hbl : bestLen < maxLen then
        data[cand + bestLen]'(by omega) != data[pos + bestLen]'(by omega)
      else false
    if skip then
      if bestLen ≥ min niceLen maxLen then bestPos * 512 + bestLen
      else chainWalkArr data c windowSize pos maxLen niceLen hpm
        (aget c (cand &&& 0x7FFF)) (fuel - 1) bestLen bestPos
    else
      let ml := lz77Greedy.countMatch data cand pos maxLen hcand hpm
      let bl := if ml > bestLen then ml else bestLen
      let bp := if ml > bestLen then cand else bestPos
      if bl ≥ min niceLen maxLen then bp * 512 + bl
      else chainWalkArr data c windowSize pos maxLen niceLen hpm
        (aget c (cand &&& 0x7FFF)) (fuel - 1) bl bp
  else bestPos * 512 + bestLen

partial def updateHashesArr (data : ByteArray) (c : Array Nat) (hashSize prevSize pos j matchLen insertCap : Nat) : Array Nat :=
  if j < matchLen ∧ j ≤ insertCap then
    if h : pos + j + 2 < data.size then
      let hsh := lz77Greedy.hash3 data (pos + j) hashSize h
      let head := aget c (prevSize + hsh)
      let c := aset (aset c (prevSize + hsh) (pos + j)) ((pos + j) &&& 0x7FFF) head
      updateHashesArr data c hashSize prevSize pos (j + 1) matchLen insertCap
    else
      updateHashesArr data c hashSize prevSize pos (j + 1) matchLen insertCap
  else c

partial def lazyLoopArr (data : ByteArray) (c : Array Nat)
    (windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth pos : Nat)
    (acc : Array UInt32) : Array UInt32 :=
  if hlt : pos + 2 < data.size then
    let h := lz77Greedy.hash3 data pos hashSize hlt
    let head := aget c (prevSize + h)
    let c := aset c (prevSize + h) pos
    let c := aset c (pos &&& 0x7FFF) head
    let maxLen := min 258 (data.size - pos)
    have hmaxLenP : pos + maxLen ≤ data.size := by omega
    let r := chainWalkArr data c windowSize pos maxLen niceLen hmaxLenP head maxChain 0 0
    let matchLen := r % 512
    let matchPos := r / 512
    if matchLen ≥ 3 then
      if pos + matchLen ≤ data.size then
        if h3lt : pos + 3 < data.size then
          if matchLen < goodMatch then
            let h2 := lz77Greedy.hash3 data (pos + 1) hashSize (by omega)
            let head2 := aget c (prevSize + h2)
            let maxLen2 := min 258 (data.size - (pos + 1))
            have hmaxLen2P : (pos + 1) + maxLen2 ≤ data.size := by omega
            let r2 := chainWalkArr data c windowSize (pos + 1) maxLen2 niceLen hmaxLen2P head2 lazyDepth 0 0
            let matchLen2 := r2 % 512
            let matchPos2 := r2 / 512
            if lazyAcceptCost matchLen (pos - matchPos) matchLen2 (pos + 1 - matchPos2) then
              if pos + 1 + matchLen2 ≤ data.size then
                let c := updateHashesArr data c hashSize prevSize pos 1 (matchLen2 + 1) insertCap
                lazyLoopArr data c windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth (pos + 1 + matchLen2)
                  (acc.push (packTok (.literal (data[pos]'(by omega)))) |>.push
                    (packTok (.reference matchLen2 (pos + 1 - matchPos2))))
              else
                let c := updateHashesArr data c hashSize prevSize pos 1 matchLen insertCap
                lazyLoopArr data c windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth (pos + matchLen)
                  (acc.push (packTok (.reference matchLen (pos - matchPos))))
            else
              let c := updateHashesArr data c hashSize prevSize pos 1 matchLen insertCap
              lazyLoopArr data c windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth (pos + matchLen)
                (acc.push (packTok (.reference matchLen (pos - matchPos))))
          else
            let c := updateHashesArr data c hashSize prevSize pos 1 matchLen insertCap
            lazyLoopArr data c windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth (pos + matchLen)
              (acc.push (packTok (.reference matchLen (pos - matchPos))))
        else
          lazyLoopArr data c windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth (pos + matchLen)
            (acc.push (packTok (.reference matchLen (pos - matchPos))))
      else
        lazyLoopArr data c windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth (pos + 1)
          (acc.push (packTok (.literal (data[pos]'(by omega)))))
    else
      lazyLoopArr data c windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth (pos + 1)
        (acc.push (packTok (.literal (data[pos]'(by omega)))))
  else
    trailingP data pos acc

/-- `Array Nat` merged lazy matcher — the control (same code as
    `packedMergedMatcher`, `Array Nat` storage). -/
def arrMergedMatcher (data : ByteArray) (maxChain : Nat) (windowSize : Nat := 32768)
    (insertCap : Nat := 1000000000) (goodMatch : Nat := 259) (niceLen : Nat := 258)
    (lazyDepth : Nat := maxChain) : Array UInt32 :=
  if data.size < 3 then
    trailingP data 0 #[]
  else
    let hashSize := 65536
    let prevSize := min chainWinSize data.size
    let c : Array Nat := .replicate (prevSize + hashSize) data.size
    lazyLoopArr data c windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth 0
      (Array.emptyWithCapacity data.size)

end Bench.PackedChain
