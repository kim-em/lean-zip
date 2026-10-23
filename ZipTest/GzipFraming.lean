import ZipTest.Helpers

/-! Native gzip framing tests: reserved FLG bits (RFC 1952 §2.3.1.2). -/

open Zip.Native

/-- A gzip header with a reserved FLG bit set is rejected, as RFC 1952
    requires; the same member with FLG = 0 decodes. -/
def ZipTest.GzipFraming.flagTests : IO Unit := do
  let payload := "gzip framing test".toUTF8
  let good := GzipEncode.compress payload 6
  match GzipDecode.decompress good with
  | .ok out => unless out == payload do throw (IO.userError "gzip flags: baseline mismatch")
  | .error e => throw (IO.userError s!"gzip flags: baseline rejected: {e}")
  for bit in [(0x20 : UInt8), 0x40, 0x80] do
    match GzipDecode.decompress (good.set! 3 bit) with
    | .ok _ => throw (IO.userError s!"gzip flags: reserved FLG bit {bit} accepted")
    | .error e =>
      unless e.contains "reserved header flag" do
        throw (IO.userError s!"gzip flags: reserved FLG bit {bit}: unexpected error: {e}")
  IO.println "Gzip framing flag tests: OK"
