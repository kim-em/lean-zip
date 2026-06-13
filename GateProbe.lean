import Zip
/-! #2537 probe (NOT committed): run the ungated optimal-parse candidate on a
    slice of a file so peak RSS can be measured externally. -/
def main (args : List String) : IO Unit := do
  let path := args[0]!
  let bytes := (args[1]!).toNat!
  let data ← IO.FS.readBinFile path
  let slice := data.extract 0 (min bytes data.size)
  let out := Zip.Native.Deflate.deflateDynamicBlocksOptimal slice
    Zip.Native.Deflate.sharedTokChunk
  IO.println s!"in {slice.size} out {out.size}"
