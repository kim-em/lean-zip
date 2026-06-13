import Zip

/-! Wave 3 Step 1 (NOT committed): isolate the 3a headroom. Three variants of
    the chain-state kernel — per simulated position: one pseudo-hash, one head
    read, two writes (head update + prev link), then a K-step chain walk of
    prev-reads with two window-guard comparisons each. All variants use the
    SAME `[..]!`/`set!` access (check overhead cancels out); they differ ONLY
    in the array element type and the guard/index arithmetic:

      A. `Array Nat`   state, `Nat`    arithmetic  (deployed shape)
      B. `Array UInt32` state, `UInt32` arithmetic
      C. `Array UInt32` state, `USize`-converted indexing arithmetic

    Each returns a sink (sum of visited candidates) — identical across
    variants by construction; printed for cross-checking. -/

def reps : Nat := 5

@[inline] def lcg (x : Nat) : Nat := (x * 1103515245 + 12345) % 65536

def runA (n walkK : Nat) : Nat := Id.run do
  let mut hashTable : Array Nat := .replicate 65536 n
  let mut prev : Array Nat := .replicate n n
  let mut acc : Nat := 0
  let mut pos : Nat := 0
  while pos < n do
    let h := lcg pos
    let head := hashTable[h]!
    hashTable := hashTable.set! h pos
    prev := prev.set! pos head
    let mut cand := head
    let mut k := walkK
    while k > 0 do
      if cand < pos ∧ pos - cand ≤ 32768 then
        acc := acc + cand
        cand := prev[cand]!
        k := k - 1
      else
        k := 0
    pos := pos + 1
  return acc

def runB (n walkK : Nat) : Nat := Id.run do
  let nU : UInt32 := UInt32.ofNat n
  let mut hashTable : Array UInt32 := .replicate 65536 nU
  let mut prev : Array UInt32 := .replicate n nU
  let mut acc : Nat := 0
  let mut posU : UInt32 := 0
  while posU < nU do
    let h := lcg posU.toNat
    let head := hashTable[h]!
    hashTable := hashTable.set! h posU
    prev := prev.set! posU.toNat head
    let mut cand := head
    let mut k := walkK
    while k > 0 do
      if cand < posU ∧ posU - cand ≤ 32768 then
        acc := acc + cand.toNat
        cand := prev[cand.toNat]!
        k := k - 1
      else
        k := 0
    posU := posU + 1
  return acc

def runC (n walkK : Nat) : Nat := Id.run do
  let nU : USize := USize.ofNat n
  let mut hashTable : Array USize := .replicate 65536 nU
  let mut prev : Array USize := .replicate n nU
  let mut acc : USize := 0
  let mut posU : USize := 0
  while posU < nU do
    let h := lcg posU.toNat
    let head := hashTable[h]!
    hashTable := hashTable.set! h posU
    prev := prev.set! posU.toNat head
    let mut cand := head
    let mut k := walkK
    while k > 0 do
      if cand < posU ∧ posU - cand ≤ 32768 then
        acc := acc + cand
        cand := prev[cand.toNat]!
        k := k - 1
      else
        k := 0
    posU := posU + 1
  return acc.toNat

def time1 (label : String) (act : Unit → Nat) : IO Float := do
  let t0 ← IO.monoNanosNow
  let mut sink := 0
  for _ in [0:reps] do
    sink := sink + act ()
  let t1 ← IO.monoNanosNow
  let ms := (Float.ofNat (t1 - t0)) / 1e6 / (Float.ofNat reps)
  IO.println s!"{label}: {ms} ms (sink {sink})"
  return ms

def main : IO Unit := do
  for (n, k) in [(2000000, 4), (2000000, 32), (8000000, 8)] do
    IO.println s!"--- n={n} walkK={k}"
    let a ← time1 "A Array Nat   /Nat   " (fun _ => runA n k)
    let b ← time1 "B Array UInt32/UInt32" (fun _ => runB n k)
    let c ← time1 "C Array USize /USize " (fun _ => runC n k)
    IO.println s!"  B/A {a/b} x    C/A {a/c} x"
