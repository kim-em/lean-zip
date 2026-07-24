import Zip.Spec.DeflateRoundtrip
import Zip.Spec.DeflateSuffix
import Zip.Spec.InflateLoopBounds
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

namespace Zip.Native.Inflate

/-- The production inflater succeeds with `output` exactly when the independent
    formal DEFLATE specification decodes the input to `output`, provided that
    `output` fits under the inflater's zip-bomb limit.

    `Deflate.Spec.DecodesTo` deliberately permits trailing data after the final
    DEFLATE block, matching `inflate`. For a predicate asserting that the input
    contains exactly one stream up to final-byte padding, use
    `Deflate.Spec.IsValidStreamFor`. -/
theorem inflate_ok_iff_decodesTo (compressed : ByteArray) (maxOutputSize : Nat)
    (output : ByteArray) (hsize : output.size ≤ maxOutputSize) :
    inflate compressed maxOutputSize = .ok output ↔
      Deflate.Spec.DecodesTo compressed output := by
  constructor
  · intro hinflate
    have href : inflateReference compressed maxOutputSize = .ok output :=
      (inflate_ok_iff_reference compressed maxOutputSize output).mp hinflate
    exact Deflate.Correctness.inflate_correct' compressed maxOutputSize output href
  · intro hspec
    have hlen : output.data.toList.length ≤ maxOutputSize := by
      simpa only [Array.length_toList, ByteArray.size_data] using hsize
    have hgo : Deflate.Spec.decode.go (Deflate.Spec.bytesToBits compressed) [] =
        some output.data.toList := by
      exact hspec
    obtain ⟨endPos, hraw⟩ :=
      Zip.Native.inflateRaw_complete compressed 0 maxOutputSize output.data.toList hlen
        (by simpa only [Nat.zero_mul, List.drop_zero] using hgo)
    have href : inflateReference compressed maxOutputSize = .ok output := by
      simp only [inflateReference, hraw, bind, Except.bind, pure, Except.pure,
        Array.toArray_toList]
    exact (inflate_ok_iff_reference compressed maxOutputSize output).mpr href

/-- Every exact valid stream is accepted by the production inflater when its
    specified output fits under the zip-bomb limit. -/
theorem inflate_of_isValidStreamFor (compressed output : ByteArray)
    (maxOutputSize : Nat) (hvalid : Deflate.Spec.IsValidStreamFor compressed output)
    (hsize : output.size ≤ maxOutputSize) :
    inflate compressed maxOutputSize = .ok output :=
  (inflate_ok_iff_decodesTo compressed maxOutputSize output hsize).mpr hvalid.decodesTo

end Zip.Native.Inflate
