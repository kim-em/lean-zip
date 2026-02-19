import ZipTest.Helpers

def ZipTest.Binary.tests : IO Unit := do
  -- Octal roundtrip
  let testOctalVal : UInt64 := 1234
  let octalBytes := Binary.writeOctal testOctalVal 12
  unless octalBytes.size == 12 do throw (IO.userError s!"octal size: {octalBytes.size}")
  let octalVal := Binary.readOctal octalBytes 0 12
  unless octalVal == testOctalVal do throw (IO.userError s!"octal val: {octalVal}")
  let octalZero : UInt64 := 0
  let zeroOctal := Binary.writeOctal octalZero 8
  unless Binary.readOctal zeroOctal 0 8 == 0 do throw (IO.userError "octal zero")

  -- Little-endian roundtrip
  let testVal16 : UInt16 := 0xABCD
  let le16 := Binary.writeUInt16LE testVal16
  unless le16.size == 2 do throw (IO.userError "le16 size")
  unless Binary.readUInt16LE le16 0 == testVal16 do throw (IO.userError "le16 val")
  let testVal32 : UInt32 := 0xDEADBEEF
  let le32 := Binary.writeUInt32LE testVal32
  unless le32.size == 4 do throw (IO.userError "le32 size")
  unless Binary.readUInt32LE le32 0 == testVal32 do throw (IO.userError "le32 val")

  -- String roundtrip
  let strBytes := Binary.writeString "hello" 10
  unless strBytes.size == 10 do throw (IO.userError "str size")
  unless Binary.readString strBytes 0 10 == "hello" do throw (IO.userError "str val")

  -- Path safety tests
  unless Binary.isPathSafe "subdir/file.txt" do throw (IO.userError "isPathSafe: normal path")
  unless Binary.isPathSafe "file.txt" do throw (IO.userError "isPathSafe: simple file")
  unless !Binary.isPathSafe "../escape" do throw (IO.userError "isPathSafe: dotdot")
  unless !Binary.isPathSafe "/etc/passwd" do throw (IO.userError "isPathSafe: absolute")
  unless !Binary.isPathSafe "a\\b" do throw (IO.userError "isPathSafe: backslash")
  unless !Binary.isPathSafe "a//b" do throw (IO.userError "isPathSafe: empty component")
  unless !Binary.isPathSafe "./foo" do throw (IO.userError "isPathSafe: dot component")
  unless !Binary.isPathSafe "C:/Windows" do throw (IO.userError "isPathSafe: drive letter")
  unless !Binary.isPathSafe "D:" do throw (IO.userError "isPathSafe: bare drive")
  IO.println "Binary tests: OK"
