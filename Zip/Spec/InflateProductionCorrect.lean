import Zip.Spec.DeflateSuffix
import Zip.Spec.InflateCorrect
import Zip.Spec.InflateLoopBounds
import Zip.Spec.InflateTreeFreeCorrect

/-!
# Production inflater correctness against the formal DEFLATE specification

The production tree-free inflater has the same accept set as the verified
reference inflater. This module packages that result against the public
`Deflate.Spec.DecodesTo` and `Deflate.Spec.IsValidStreamFor` predicates.
-/

namespace Zip.Native.Inflate

/-- Successful production inflation implies decoding by the independent formal
    DEFLATE specification. This direction does not require the caller to recover
    the inflater's output-size invariant. -/
theorem decodesTo_of_inflate_eq_ok (compressed : ByteArray) (maxOutputSize : Nat)
    (output : ByteArray) (hinflate : inflate compressed maxOutputSize = .ok output) :
    Deflate.Spec.DecodesTo compressed output := by
  have href : inflateReference compressed maxOutputSize = .ok output :=
    (inflate_ok_iff_reference compressed maxOutputSize output).mp hinflate
  exact (Deflate.Spec.decodesTo_iff compressed output).mpr
    (Deflate.Correctness.inflate_correct' compressed maxOutputSize output href)

/-- The production inflater succeeds with `output` exactly when the independent
    formal DEFLATE specification decodes the input to `output`, provided that
    `output` fits under the inflater's zip-bomb limit. The size hypothesis is
    needed only for the spec-to-inflater direction; use
    `decodesTo_of_inflate_eq_ok` for the unconditional inflater-to-spec direction.

    `Deflate.Spec.DecodesTo` deliberately permits trailing data after the final
    DEFLATE block, matching `inflate`. For a predicate asserting that the input
    contains exactly one stream up to final-byte padding, use
    `Deflate.Spec.IsValidStreamFor`. -/
theorem inflate_ok_iff_decodesTo (compressed : ByteArray) (maxOutputSize : Nat)
    (output : ByteArray) (hsize : output.size ≤ maxOutputSize) :
    inflate compressed maxOutputSize = .ok output ↔
      Deflate.Spec.DecodesTo compressed output := by
  constructor
  · exact decodesTo_of_inflate_eq_ok compressed maxOutputSize output
  · intro hspec
    have hlen : output.data.toList.length ≤ maxOutputSize := by
      simpa only [Array.length_toList, ByteArray.size_data] using hsize
    have hdecode := (Deflate.Spec.decodesTo_iff compressed output).mp hspec
    have hgo : Deflate.Spec.decode.go (Deflate.Spec.bytesToBits compressed) [] =
        some output.data.toList := by
      simpa only [Deflate.Spec.decode] using hdecode
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
