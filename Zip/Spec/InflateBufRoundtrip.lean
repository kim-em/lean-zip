import Zip.Spec.InflateBufCorrect
import Zip.Spec.DeflateFixedCorrect

/-!
# Roundtrip for the wide-buffer decoder

`InflateBuf.inflate` (the wide-buffer DEFLATE decompressor) inverts the native
fixed-Huffman compressor `deflateFixed`, by transferring `Inflate`'s roundtrip
theorem across the proven equality `InflateBuf.inflate = Inflate.inflate`.
-/

namespace Zip.Native.InflateBuf

/-- **Roundtrip:** the wide-buffer `inflate` inverts `deflateFixed`. -/
theorem inflate_deflateFixed (data : ByteArray) (maxOut : Nat) (hsize : data.size ≤ maxOut) :
    InflateBuf.inflate (Zip.Native.Deflate.deflateFixed data) maxOut = .ok data := by
  rw [inflate_eq]
  exact Zip.Native.Deflate.inflate_deflateFixed data maxOut hsize

end Zip.Native.InflateBuf
