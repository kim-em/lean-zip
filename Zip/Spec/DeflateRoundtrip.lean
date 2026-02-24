import Zip.Spec.DeflateFixedCorrect
import Zip.Spec.DeflateDynamicCorrect

/-!
# Unified DEFLATE Roundtrip (Phase 4 Capstone)

Defines `deflateRaw`, a unified dispatch function that selects the
compression strategy based on level (0 = stored, 1 = fixed Huffman,
2-4 = lazy LZ77 + fixed, 5+ = dynamic Huffman), and proves the
unified roundtrip theorem: `inflate (deflateRaw data level) = .ok data`.

This composes the per-level roundtrip theorems:
- `inflate_deflateStoredPure` (Level 0)
- `inflate_deflateFixed` (Level 1)
- `inflate_deflateLazy` (Levels 2-4)
- `inflate_deflateDynamic` (Levels 5+)
-/

namespace Zip.Native.Deflate

open Zip.Spec.DeflateStoredCorrect (deflateStoredPure inflate_deflateStoredPure)

/-- Unified raw DEFLATE compression dispatch.
    Level 0 = stored, 1 = fixed Huffman, 2-4 = lazy LZ77, 5+ = dynamic Huffman. -/
def deflateRaw (data : ByteArray) (level : UInt8 := 6) : ByteArray :=
  if level == 0 then deflateStoredPure data
  else if level == 1 then deflateFixed data
  else if level < 5 then deflateLazy data
  else deflateDynamic data

/-- Unified DEFLATE roundtrip: inflate ∘ deflateRaw = identity.
    This is the Phase 4 capstone theorem from VERIFICATION.md.
    The size bound (5M) is the tightest across all compression levels,
    arising from the lazy LZ77 path (levels 2-4). -/
theorem inflate_deflateRaw (data : ByteArray) (level : UInt8)
    (hsize : data.size < 5000000) :
    Zip.Native.Inflate.inflate (deflateRaw data level) = .ok data := by
  unfold deflateRaw
  split
  · exact inflate_deflateStoredPure data (by omega)
  · split
    · exact inflate_deflateFixed data (by omega)
    · split
      · exact inflate_deflateLazy data hsize
      · exact inflate_deflateDynamic data (by omega)

end Zip.Native.Deflate
