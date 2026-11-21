import ZipTest.Helpers

/-! Regression tests for the inclusive 1000-member gzip concatenation limit. -/

namespace ZipTest.GzipMemberLimit

private def repeatMember (member : ByteArray) (count : Nat) : ByteArray := Id.run do
  let mut stream := ByteArray.empty
  for _ in [:count] do
    stream := stream ++ member
  return stream

private def repeatPayload (payload : ByteArray) (count : Nat) : ByteArray := Id.run do
  let mut output := ByteArray.empty
  for _ in [:count] do
    output := output ++ payload
  return output

def tests : IO Unit := do
  IO.println "  GzipMemberLimit (concatenated member boundary) tests..."
  let payload := ByteArray.mk #[0x42]
  let member := Zip.Native.GzipEncode.compress payload 0

  -- The member-count cap is inclusive: 999 and 1000 complete members pass.
  let belowLimit := repeatMember member 999
  match Zip.Native.GzipDecode.decompress belowLimit with
  | .ok output =>
    unless output.beq (repeatPayload payload 999) do
      throw (IO.userError "gzip member limit: 999-member output mismatch")
  | .error e =>
    throw (IO.userError s!"gzip member limit: 999 members were rejected: {e}")

  let atLimit := repeatMember member 1000
  match Zip.Native.GzipDecode.decompress atLimit with
  | .ok output =>
    unless output.beq (repeatPayload payload 1000) do
      throw (IO.userError "gzip member limit: 1000-member output mismatch")
  | .error e =>
    throw (IO.userError s!"gzip member limit: 1000 members were rejected: {e}")

  -- A 1001st valid member must still hit the bounded-loop rejection.
  let aboveLimit := atLimit ++ member
  match Zip.Native.GzipDecode.decompress aboveLimit with
  | .error e =>
    unless e.contains "too many concatenated members" do
      throw (IO.userError s!"gzip member limit: unexpected 1001-member error: {e}")
  | .ok _ =>
    throw (IO.userError "gzip member limit: 1001 members were accepted")

  IO.println "  GzipMemberLimit tests passed."

end ZipTest.GzipMemberLimit
