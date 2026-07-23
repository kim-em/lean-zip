import Zip.Spec.DeflateRoundtrip
import Zip.Spec.InflateTreeFreeCorrect

/-!
# Roundtrip through the production decoder

`inflate_deflateRaw` states the unified DEFLATE roundtrip against the verified
reference decoder `Inflate.inflateReference`. The production decoder
`Inflate.inflate` has the same accept set (`inflate_ok_iff_reference`), so the
roundtrip transfers. This corollary states it directly: inflating what we
deflate with the decoder we actually ship returns the input exactly. It is the
form quoted in expository material, where the `Reference` distinction is
noise.
-/

namespace Zip.Native.Deflate

/-- Unified DEFLATE roundtrip through the **production** decoder: inflating
    what we deflate returns the input exactly. Corollary of
    `inflate_deflateRaw` via the accept-set equality
    `Inflate.inflate_ok_iff_reference`. -/
theorem inflate_deflateRaw' (data : ByteArray) (level : UInt8)
    (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
    Zip.Native.Inflate.inflate (deflateRaw data level) maxOutputSize = .ok data :=
  (Zip.Native.Inflate.inflate_ok_iff_reference _ _ _).mpr
    (inflate_deflateRaw data level maxOutputSize hsize)

end Zip.Native.Deflate
