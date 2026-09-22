import Zip.Native.DeflateDynamic

/-!
# Opt-in multi-threaded DEFLATE — implementation

`deflateDynamicBlocksSCParallel` is `deflateDynamicBlocksSC` plus one argument, a
threading flag.  With `par = false` it *is* that call: no chunk list, no
task, nothing to prune.  With `par = true` each chunk is matched **and emitted**
into its own `BitWriter` on its own task, and those writers are merged in order
by `appendW`, a bit-level concatenation.

The correctness proofs live in `Zip/Spec/ParallelCorrect.lean`, which shows the
output is byte-identical to `deflateDynamicBlocksSC` for every flag, chunk size
and level, and restates `deflateDynamicBlocksSC`'s theorems for it.
-/

namespace Zip.Native.BitWriter

/-- Append `b`'s whole bytes from index `i` onto `a`, eight bits at a time. -/
def appendBytesFrom (a : BitWriter) (b : ByteArray) (i : Nat) : BitWriter :=
  if h : i < b.size then appendBytesFrom (a.writeBits 8 b[i].toUInt32) b (i + 1) else a
termination_by b.size - i

/-- Append `b`'s `n` pending bits (LSB first) onto `a`, one at a time. -/
def appendPending (a : BitWriter) (buf : UInt64) (n i : Nat) : BitWriter :=
  if i < n then
    appendPending (a.writeBits 1 (cond (buf.toNat.testBit i) 1 0)) buf n (i + 1)
  else a
termination_by n - i

/-- Append every bit of `b` onto `a`. -/
def appendW (a b : BitWriter) : BitWriter :=
  appendPending (appendBytesFrom a b.data 0) b.bitBuf b.bitCount.toNat 0

end Zip.Native.BitWriter

namespace Zip.Native.Deflate
open Zip.Native.BitWriter

/-- One chunk's block, emitted into its own writer — the unit of parallel work. -/
def chunkFrag (data : ByteArray) (level : UInt8) (pos j : Nat) (isFinal : Bool) : BitWriter :=
  emitChunkBlock BitWriter.empty data pos j level isFinal

/-- One writer-producing task per chunk, in visit order. -/
def chunkWriters (data : ByteArray) (chunkSize : Nat) (level : UInt8)
    (pos : Nat) : List (Task BitWriter) :=
  if pos ≥ data.size then []
  else
    let j := min (pos + max chunkSize 1) data.size
    (Task.spawn fun _ => chunkFrag data level pos j (decide (j ≥ data.size))) ::
      chunkWriters data chunkSize level j
termination_by data.size - pos
decreasing_by simp_all only [Nat.not_le]; omega

/-- **Chunked DEFLATE with a threading flag.**  Sequential by default; with
    `par := true` each chunk is matched and emitted on its own task.  Each chunk
    is one task, so pick `chunkSize` well above the 32 KiB window (256 KiB works
    well); `0` is treated as `1`, correct but one task per byte. -/
def deflateDynamicBlocksSCParallel (data : ByteArray) (chunkSize : Nat) (level : UInt8)
    (par : Bool := false) : ByteArray :=
  if par then
    if data.size == 0 then deflateDynamicBlocksSC data chunkSize level
    else ((chunkWriters data chunkSize level 0).foldl
      (fun w t => appendW w t.get) BitWriter.empty).flush
  else deflateDynamicBlocksSC data chunkSize level

end Zip.Native.Deflate
