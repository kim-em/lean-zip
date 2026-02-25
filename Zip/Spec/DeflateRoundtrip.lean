import Zip.Spec.DeflateFixedCorrect
import Zip.Spec.DeflateDynamicCorrect

/-!
# Unified DEFLATE Roundtrip (Phase B4 Capstone)

Proves the unified roundtrip theorem for `deflateRaw`:
`inflate (deflateRaw data level) = .ok data`.

`deflateRaw` is defined in `Zip/Native/DeflateDynamic.lean` and selects the
compression strategy based on level (0 = stored, 1 = fixed Huffman,
2-4 = lazy LZ77 + fixed, 5+ = dynamic Huffman).

This composes the per-level roundtrip theorems:
- `inflate_deflateStoredPure` (Level 0)
- `inflate_deflateFixed` (Level 1)
- `inflate_deflateLazy` (Levels 2-4)
- `inflate_deflateDynamic` (Levels 5+)
-/

namespace Zip.Native.Deflate

open Zip.Spec.DeflateStoredCorrect (inflate_deflateStoredPure)

/-- Unified DEFLATE roundtrip: inflate ∘ deflateRaw = identity.
    This is the Phase B4 capstone theorem from PLAN.md.
    The size bound (500M) is the tightest across all compression levels,
    arising from the lazy LZ77 path (levels 2-4). -/
theorem inflate_deflateRaw (data : ByteArray) (level : UInt8)
    (hsize : data.size < 500000000) :
    Zip.Native.Inflate.inflate (deflateRaw data level) = .ok data := by
  unfold deflateRaw
  split
  · exact inflate_deflateStoredPure data (by omega)
  · split
    · exact inflate_deflateFixedIter data (by omega)
    · split
      · exact inflate_deflateLazy data hsize
      · exact inflate_deflateDynamic data (by omega)

end Zip.Native.Deflate
