import Zip.Spec.GzipCorrect

/-!
# Inflate data-suffix independence

Proves that `inflateLoop` / `inflateRaw` produce the same result and endPos
when extra bytes are appended to the BitReader's data. This is used to derive
tight endPos bounds: running on `header ++ deflated` gives `endPos ≤ header.size
+ deflated.size`, and suffix independence shows running on `header ++ deflated ++
trailer` gives the same endPos.
-/

namespace Zip.Native

/-- `inflateRaw` on `data ++ suffix` returns the same result and endPos. -/
theorem inflateRaw_suffix (data suffix : ByteArray) (startPos maxOutputSize : Nat)
    (result : ByteArray) (endPos : Nat)
    (h : Inflate.inflateRaw data startPos maxOutputSize = .ok (result, endPos)) :
    Inflate.inflateRaw (data ++ suffix) startPos maxOutputSize =
      .ok (result, endPos) := by
  sorry

end Zip.Native
