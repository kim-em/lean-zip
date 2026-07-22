import Zip

/-! # lazy2-sweep — matcher accept-rule + two-position-lookahead spike (#2765)

Measurement-first probe for issue #2765: does swapping the lazy matcher's
conservative "longer AND no-farther" accept rule for libdeflate's cost-based
rule, and/or adding a second (`pos+2`) lookahead probe, close any of the
remaining L7/L8 ratio distance to zlib/libdeflate?

The spike is deliberately bench-only: it reimplements the boxed lazy matcher
(`lz77ChainLazy`) with the accept rule and lookahead depth as parameters,
using only public primitives (`lz77Chain.chainWalk`, `lz77Chain.updateHashes`,
`headProbeGuarded`, `guardedSet`, `lz77Greedy.{hash3,trailing}`), so no proven
code is touched until a variant earns a place. Sizes are computed through the
*exact* L6–L8 dispatch `deflateRaw` uses (base-vs-observation-split, size
arbitrated), so the reported bytes are what the shipped encoder would emit for
each token stream.

Variants measured per (file, level ∈ {7,8}):

  * `prod`   — production `lzMatchP` (the shipped packed matcher), the ground
               truth baseline.
  * `mirror` — boxed reimplementation with the *production* heuristics
               (conservative accept, one-step lazy, half-depth probe). A faithful
               mirror emits byte-identically to `prod`; the row exists to certify
               the reimplementation before trusting the variant deltas.
  * `cost`   — cost-based accept rule (libdeflate first step,
               `4·Δlen + bsr(d1) − bsr(d2) > 2`), one-step lazy.
  * `lazy2`  — two-position lookahead (`pos+1` half depth, `pos+2` quarter depth),
               conservative accept.
  * `l2cost` — two-position lookahead + cost accept (first step `> 2`, second `> 6`).

Modeling notes (bench approximation, not a claim of libdeflate byte-identity):
the `pos+2` probe runs against the hash state with `pos` inserted but `pos+1`
not (mirrors the one-step lazy's "don't insert the lookahead position" policy);
the two-deep lookahead is a bounded best-of-{pos,pos+1,pos+2} cascade rather
than libdeflate's rolling deferral. The spike measures whether the lever moves
ratio at all, cheaply — a landed version would be exact.

    <file>,<level>,<variant>,<inBytes>,<outBytes>

Usage: lake -d bench exe lazy2-sweep <file> [<file> ...]
-/

open Zip.Native.Deflate

namespace ZipLazy2Sweep

/-- `bsr32 x = ⌊log2 x⌋` for `x ≥ 1` — the index of the high set bit, i.e. the
    number of extra offset bits libdeflate's cost rule charges for a distance. -/
@[inline] def bsr (x : Nat) : Nat := Nat.log2 x

/-- libdeflate cost accept: prefer the later match `(len2,dist2)` over the current
    `(len1,dist1)` when it is strictly longer and the length gain (×4) outweighs the
    extra offset bits beyond `thr`. Written with additions on both sides to avoid
    `Nat` truncation. -/
@[inline] def acceptCost (thr len1 dist1 len2 dist2 : Nat) : Bool :=
  len2 > len1 && 4 * (len2 - len1) + bsr dist1 > thr + bsr dist2

/-- Conservative accept (our production rule): strictly longer and no farther. -/
@[inline] def acceptCons (len1 dist1 len2 dist2 : Nat) : Bool :=
  len2 > len1 && dist2 ≤ dist1

/-- Parameterized boxed lazy matcher.

    `costAccept` selects the accept rule; `useLazy2` enables the `pos+2` probe.
    `chain`/`lazyD`/`lazyD2` are the depths for the `pos`/`pos+1`/`pos+2` walks.
    Produces the same `Array LZ77Token` shape as `lz77ChainLazy`. `partial`
    (bench-only) so the spike carries no termination obligation. -/
partial def lazyGen
    (costAccept useLazy2 : Bool)
    (data : ByteArray) (chain lazyD lazyD2 insertCap goodMatch niceLen windowSize hashSize : Nat)
    (hashTable prev : Array Nat) (pos : Nat) (acc : Array LZ77Token) : Array LZ77Token :=
  if hlt : pos + 2 < data.size then
    let h := lz77Greedy.hash3 data pos hashSize hlt
    let head := headProbeGuarded hashTable h
    let hashTable := guardedSet hashTable h pos
    let prev := guardedSet prev (pos &&& 0x7FFF) head
    let maxLen := min 258 (data.size - pos)
    have hmaxLenP : pos + maxLen ≤ data.size := by omega
    let m := lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hmaxLenP head chain 0 0
    let matchLen := m.1
    let matchPos := m.2
    let dist1 := pos - matchPos
    -- Fall back to a literal when there is no usable match at `pos`.
    if matchLen ≥ 3 ∧ pos + matchLen ≤ data.size then
      -- Thunked so the eager `let` does not force the whole rest-of-file tail at
      -- every position (a strict `let` binding a recursive call is exponential).
      let emitMatchAtPos : Unit → Array LZ77Token := fun _ =>
        let (hashTable, prev) := lz77Chain.updateHashes data hashSize hashTable prev pos 1 matchLen insertCap
        lazyGen costAccept useLazy2 data chain lazyD lazyD2 insertCap goodMatch niceLen windowSize hashSize
          hashTable prev (pos + matchLen) (acc.push (.reference matchLen dist1))
      if h3lt : pos + 3 < data.size then
        if matchLen < goodMatch then
          -- probe pos+1 at half depth
          let h2 := lz77Greedy.hash3 data (pos + 1) hashSize (by omega)
          let head2 := headProbeGuarded hashTable h2
          let maxLen2 := min 258 (data.size - (pos + 1))
          have hmaxLen2P : (pos + 1) + maxLen2 ≤ data.size := by omega
          let m2 := lz77Chain.chainWalk data prev windowSize (pos + 1) maxLen2 niceLen hmaxLen2P head2 lazyD 0 0
          let matchLen2 := m2.1
          let matchPos2 := m2.2
          let dist2 := (pos + 1) - matchPos2
          let accept1 := if costAccept then acceptCost 2 matchLen dist1 matchLen2 dist2
                         else acceptCons matchLen dist1 matchLen2 dist2
          if accept1 ∧ pos + 1 + matchLen2 ≤ data.size then
            -- deferred to pos+1; optionally probe pos+2 at quarter depth
            if huse : useLazy2 ∧ pos + 4 < data.size ∧ matchLen2 < goodMatch then
              let h3 := lz77Greedy.hash3 data (pos + 2) hashSize (by omega)
              let head3 := headProbeGuarded hashTable h3
              let maxLen3 := min 258 (data.size - (pos + 2))
              have hmaxLen3P : (pos + 2) + maxLen3 ≤ data.size := by omega
              let m3 := lz77Chain.chainWalk data prev windowSize (pos + 2) maxLen3 niceLen hmaxLen3P head3 lazyD2 0 0
              let matchLen3 := m3.1
              let matchPos3 := m3.2
              let dist3 := (pos + 2) - matchPos3
              let accept2 := if costAccept then acceptCost 6 matchLen2 dist2 matchLen3 dist3
                             else acceptCons matchLen2 dist2 matchLen3 dist3
              if accept2 ∧ pos + 2 + matchLen3 ≤ data.size then
                -- lit(pos) lit(pos+1) ref(pos+2)
                let (hashTable, prev) := lz77Chain.updateHashes data hashSize hashTable prev pos 1 (matchLen3 + 2) insertCap
                lazyGen costAccept useLazy2 data chain lazyD lazyD2 insertCap goodMatch niceLen windowSize hashSize
                  hashTable prev (pos + 2 + matchLen3)
                  (acc.push (.literal (data[pos]'(by omega)))
                     |>.push (.literal (data[pos + 1]'(by omega)))
                     |>.push (.reference matchLen3 dist3))
              else
                let (hashTable, prev) := lz77Chain.updateHashes data hashSize hashTable prev pos 1 (matchLen2 + 1) insertCap
                lazyGen costAccept useLazy2 data chain lazyD lazyD2 insertCap goodMatch niceLen windowSize hashSize
                  hashTable prev (pos + 1 + matchLen2)
                  (acc.push (.literal (data[pos]'(by omega))) |>.push (.reference matchLen2 dist2))
            else
              let (hashTable, prev) := lz77Chain.updateHashes data hashSize hashTable prev pos 1 (matchLen2 + 1) insertCap
              lazyGen costAccept useLazy2 data chain lazyD lazyD2 insertCap goodMatch niceLen windowSize hashSize
                hashTable prev (pos + 1 + matchLen2)
                (acc.push (.literal (data[pos]'(by omega))) |>.push (.reference matchLen2 dist2))
          else
            emitMatchAtPos ()
        else
          emitMatchAtPos ()
      else
        emitMatchAtPos ()
    else
      lazyGen costAccept useLazy2 data chain lazyD lazyD2 insertCap goodMatch niceLen windowSize hashSize
        hashTable prev (pos + 1) (acc.push (.literal (data[pos]'(by omega))))
  else
    acc ++ (lz77Greedy.trailing data pos).toArray

/-- Run the parameterized matcher over `data` with the given knobs, returning
    the boxed token stream. -/
def runMatcher (costAccept useLazy2 : Bool) (data : ByteArray)
    (chain lazyD lazyD2 insertCap goodMatch niceLen : Nat) : Array LZ77Token :=
  if data.size < 3 then
    (lz77Greedy.trailing data 0).toArray
  else
    let hashSize := 65536
    lazyGen costAccept useLazy2 data chain lazyD lazyD2 insertCap goodMatch niceLen 32768 hashSize
      (.replicate hashSize data.size) (.replicate (min chainWinSize data.size) data.size) 0 #[]

/-- Compressed size of a packed token stream through the *exact* dispatch
    `deflateRaw` uses at `level`: levels 4–5 emit a single `deflateRawBase`
    block; levels 6–8 arbitrate base against the observation-divergence split. -/
def sizeAt (data : ByteArray) (level : UInt8) (ptoks : TokenArray) : Nat :=
  if level < 6 then
    (deflateRawBasePPrep data ptoks).1
  else
    let basePrep := deflateRawBasePPrep data ptoks
    let cuts := chooseSplitsHeuristicP ptoks data.size
    let withObs : Nat × (Unit → ByteArray) :=
      if cuts.isEmpty then basePrep
      else
        let obsPrep := deflateDynamicBlocksSharedAtSizedP data ptoks cuts
        if basePrep.1 < obsPrep.1 then basePrep else obsPrep
    withObs.1

/-- Pack an `Array UInt32` of already-packed words into a `TokenArray` (bench-only:
    the boxed variant matchers emit `Array UInt32`, which the size path now
    consumes as a `TokenArray`). -/
def packedToTA (a : Array UInt32) : TokenArray :=
  a.foldl (·.push ·) (TokenArray.emptyWithCapacity a.size)

/-- Size a boxed token stream (variant matchers emit boxed tokens; `packTok`
    maps them to the packed words the size path consumes). -/
def sizeBoxed (data : ByteArray) (level : UInt8) (toks : Array LZ77Token) : Nat :=
  sizeAt data level (packedToTA (toks.map packTok))

def levels : List UInt8 := [4, 5, 6, 7, 8]

def runFile (path : String) : IO Unit := do
  let data ← IO.FS.readBinFile path
  let p := System.FilePath.mk path
  let label := match p.parent >>= (·.fileName), p.fileName with
    | some d, some f => s!"{d}/{f}"
    | _, some f => f
    | _, _ => path
  for level in levels do
    let chain := chainDepth level
    let ic := insertCap level
    let gm := goodMatch level
    let nl := niceLen level
    let ld := lazyDepth level          -- half depth (production)
    let ld2 := chain / 4               -- quarter depth (libdeflate second probe)
    let row (v : String) (sz : Nat) : IO Unit :=
      IO.println s!"{label},{level},{v},{data.size},{sz}"
    row "prod" (sizeAt data level (lzMatchP data level))
    row "mirror" (sizeBoxed data level (runMatcher false false data chain ld ld ic gm nl))
    row "cost"   (sizeBoxed data level (runMatcher true  false data chain ld ld ic gm nl))
    row "lazy2"  (sizeBoxed data level (runMatcher false true  data chain ld ld2 ic gm nl))
    row "l2cost" (sizeBoxed data level (runMatcher true  true  data chain ld ld2 ic gm nl))
    (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  for path in args do
    runFile path

end ZipLazy2Sweep

def main (args : List String) : IO Unit := ZipLazy2Sweep.main args
