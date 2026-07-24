import Zip.Spec.DeflateRoundtrip
import Zip.Spec.InflateProductionCorrect
import Zip.Spec.InflateTreeFreeCorrect

/-!
# Roundtrip through the production decoder

`inflateReference_deflateRaw` (`Zip/Spec/DeflateRoundtrip.lean`) states the
unified DEFLATE roundtrip against the verified reference decoder
`Inflate.inflateReference`. The production decoder `Inflate.inflate` — the
tree-free counterpart we actually ship — has the same accept set
(`inflate_ok_iff_reference`), so the roundtrip transfers verbatim.

`inflate_deflateRaw`, below, is that transferred statement: inflating what we
deflate, with the decoder we actually ship, returns the input exactly. It is the
capstone form quoted in expository material, where the `Reference` distinction is
noise.
-/

namespace Zip.Native.Deflate

/-- **Unified DEFLATE roundtrip: inflating what we deflate returns the input
    exactly.** Stated against the production decoder `Inflate.inflate` (the
    tree-free decoder we ship), for any `maxOutputSize` large enough to hold the
    input. A direct corollary of the reference-decoder capstone
    `inflateReference_deflateRaw` via the accept-set equality
    `Inflate.inflate_ok_iff_reference`. -/
theorem inflate_deflateRaw (data : ByteArray) (level : UInt8)
    (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
    Zip.Native.Inflate.inflate (deflateRaw data level) maxOutputSize = .ok data :=
  (Zip.Native.Inflate.inflate_ok_iff_reference _ _ _).mpr
    (inflateReference_deflateRaw data level maxOutputSize hsize)

end Zip.Native.Deflate
