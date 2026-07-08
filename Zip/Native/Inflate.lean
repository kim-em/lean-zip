import ZipCommon.Spec.BitReaderInvariant
import Zip.Spec.Huffman
import Zip.Native.CopyWithin
import Zip.Native.ExtendWithin

/-!
  Pure Lean DEFLATE decompressor (RFC 1951).

  Supports all three block types:
  - Type 0: Stored (uncompressed)
  - Type 1: Fixed Huffman codes
  - Type 2: Dynamic Huffman codes

  This is a reference implementation prioritizing correctness over speed.
-/

namespace Zip.Native

open ZipCommon (BitReader)

/-- Allocation-light `BitReader.readBits`: thread the cursor `(pos, bitOff)` as
    unboxed `Nat`s and build the `BitReader` struct **once** at the end, instead
    of allocating a fresh `BitReader` (+ `Except`/pair) on every bit as the
    `readBit`-looping `BitReader.readBits` does. Same per-bit byte reads, but a
    whole `n`-bit field now costs O(1) heap allocations instead of O(n). Proven
    equal to `BitReader.readBits` (`readBitsFast_eq`); used on the hot
    extra-bits path in `decodeHuffmanFast`. -/
def readBitsFast (br : BitReader) (n : Nat) : Except String (UInt32 × BitReader) :=
  go br.pos br.bitOff 0 0 n
where
  go (pos bitOff : Nat) (acc : UInt32) (shift : Nat) :
      Nat → Except String (UInt32 × BitReader)
    | 0 => .ok (acc, { br with pos := pos, bitOff := bitOff })
    | k + 1 =>
      if h : pos ≥ br.data.size then .error "BitReader: unexpected end of input"
      else
        let bit : UInt32 := (((br.data[pos]'(by omega)).toUInt32 >>> bitOff.toUInt32) &&& 1)
        if bitOff + 1 ≥ 8 then
          go (pos + 1) 0 (acc ||| (bit <<< shift.toUInt32)) (shift + 1) k
        else
          go pos (bitOff + 1) (acc ||| (bit <<< shift.toUInt32)) (shift + 1) k

/-- A Huffman tree for decoding DEFLATE symbols.
    Leaf holds a symbol value; Node branches on 0 (left) vs 1 (right). -/
inductive HuffTree where
  | leaf (symbol : UInt16)
  | node (zero : HuffTree) (one : HuffTree)
  | empty

namespace HuffTree

/-- Insert a symbol into the tree at the given code/length. -/
def insert (tree : HuffTree) (code : UInt32) (len : Nat) (symbol : UInt16) : HuffTree :=
  go tree len
where
  go (t : HuffTree) : Nat → HuffTree
    | 0 => .leaf symbol
    | n + 1 =>
      let bit := (code >>> n.toUInt32) &&& 1
      match t with
      | .empty =>
        if bit == 0 then .node (go .empty n) .empty
        else .node .empty (go .empty n)
      | .node z o =>
        if bit == 0 then .node (go z n) o
        else .node z (go o n)
      | .leaf s => .leaf s  -- shouldn't happen in valid data

/-- Build a Huffman tree by sequentially inserting symbols from an array of
    code lengths, starting from index `start`. Returns the tree and updated
    nextCode array. Used by `fromLengths` for the final insertion pass. -/
def insertLoop (lengths : Array UInt8) (nextCode : Array UInt32)
    (start : Nat) (tree : HuffTree) : HuffTree × Array UInt32 :=
  if h : start < lengths.size then
    let len := lengths[start]
    if len > 0 then
      if hlen : len.toNat < nextCode.size then
        let c := nextCode[len.toNat]
        let tree' := tree.insert c len.toNat start.toUInt16
        let nextCode' := nextCode.set! len.toNat (c + 1)
        insertLoop lengths nextCode' (start + 1) tree'
      else
        insertLoop lengths nextCode (start + 1) tree
    else
      insertLoop lengths nextCode (start + 1) tree
  else (tree, nextCode)
termination_by lengths.size - start

/-- The Huffman tree built by the canonical construction (RFC 1951 §3.2.2),
    without input validation. -/
def fromLengthsTree (lengths : Array UInt8) (maxBits : Nat := 15) : HuffTree :=
  let lsList := lengths.toList.map UInt8.toNat
  let blCount := Huffman.Spec.countLengths lsList maxBits
  let ncNat := Huffman.Spec.nextCodes blCount maxBits
  let nextCode : Array UInt32 := ncNat.map fun n => n.toUInt32
  (insertLoop lengths nextCode 0 .empty).1

/-- Build a Huffman tree from an array of code lengths (indexed by symbol).
    Symbols with length 0 have no code. Uses the canonical Huffman algorithm
    from RFC 1951 §3.2.2. Validates that all lengths are ≤ maxBits and the
    Kraft inequality is satisfied (codes are not oversubscribed). -/
def fromLengths (lengths : Array UInt8) (maxBits : Nat := 15) :
    Except String HuffTree :=
  if lengths.any (fun l => l.toNat > maxBits) then
    .error "Inflate: code length exceeds maximum"
  else
    let lsList := lengths.toList.map UInt8.toNat
    let kraft := (lsList.filter (· != 0)).foldl
      (fun acc l => acc + 2 ^ (maxBits - l)) 0
    if kraft > 2 ^ maxBits then
      .error "Inflate: oversubscribed Huffman code"
    else
      .ok (fromLengthsTree lengths maxBits)

/-- Decode one symbol from the bit reader using this Huffman tree. -/
def decode (tree : HuffTree) (br : BitReader) :
    Except String (UInt16 × BitReader) :=
  go tree br 0
where
  go : HuffTree → BitReader → Nat → Except String (UInt16 × BitReader)
    | .leaf s, br, _ => .ok (s, br)
    | .empty, _, _ => .error "Inflate: invalid Huffman code"
    | .node z o, br, n =>
      if n > 20 then .error "Inflate: Huffman decode exceeded max depth"
      else do
        let (bit, br') ← br.readBit
        if bit == 0 then go z br' (n + 1) else go o br' (n + 1)

/-! ## Table-driven fast decode (RFC 1951, "fast bits")

The bit-by-bit tree walk in `decode` descends one node per bit. The standard
DEFLATE speedup is a **lookup table**: peek `fastBits` bits and read the
`(symbol, codeLen)` directly from a `2^fastBits`-entry table, then consume
`codeLen` bits in one step. Codes longer than `fastBits` (rare; DEFLATE allows
up to 15) fall back to the tree walk. `decode` stays the canonical spec;
`decodeWithTable` is *proven equal* to it (`Zip.Spec.InflateTable`,
`decodeWithTable_eq`) and the fast block loop `decodeHuffmanFast` is proven
equal to `decodeHuffman` — there is no `@[implemented_by]` trust gap. -/

/-- Number of bits the fast decode table indexes on (the common "fast bits").
    Widened to libdeflate's `LITLEN_TABLEBITS = 11`: fewer codewords spill to the
    slow/subtable path, and the canonical O(2^bits) table build (#2671) keeps the
    wider table cheap to construct. -/
def fastBits : Nat := 11

/-- Walk `tree` using the low bits of `idx` (LSB first, matching `readBit`),
    for up to `fastBits` steps. Returns `(symbol, codeLen)` if a leaf is reached
    within `fastBits` bits, or `(0, 0)` (a sentinel meaning "fall back to the
    tree walk") for the `empty` slot or a code longer than `fastBits`. -/
def tableEntry (tree : HuffTree) (idx : Nat) : UInt16 × UInt8 :=
  go tree idx 0
where
  go (t : HuffTree) (bits depth : Nat) : UInt16 × UInt8 :=
    match t with
    | .leaf s => (s, depth.toUInt8)
    | .empty => (0, 0)
    | .node z o =>
      if depth ≥ fastBits then (0, 0)
      else if bits % 2 == 0 then go z (bits / 2) (depth + 1)
      else go o (bits / 2) (depth + 1)

/-- Pack a slot's `(symbol, codeLen)` into one `UInt32` word: the codeword length
    in the low byte (bits 0–7), the 16-bit symbol in bits 8–23. libdeflate-style
    single-word entry (libdeflate also uses a `u32`). The source reads the slot
    through `lenAt`/`symAt`, which name the same `packed[idx]!` element; the
    compiler CSEs the shared read, so a per-symbol decode lowers to **one**
    `lean_array_get` plus register shifts (verified in the generated C for the
    fastloop literal path), rather than two reads into the parallel `syms`/`lens`
    arrays of #2650 (which also touched two cache lines). Even without the CSE it
    is two reads of one tagged-scalar array, never the old two-array / two-cache-
    line shape.

    **`UInt32`, not `UInt64`.** On a 64-bit target `lean_box_uint32` is a tagged
    scalar stored inline in the array (no allocation), exactly like the old
    `Array UInt8`/`Array UInt16`; `lean_box_uint64` instead heap-allocates a boxed
    word per entry, so an `Array UInt64` would pointer-chase through `lean_ctor_get`
    on every read — re-introducing the very boxing #2650 removed. A `UInt32` holds
    len (8 bits) + symbol (16 bits) with room to spare.

    **The length is the low byte deliberately.** Only the length flows into the
    well-founded recursions' termination measure (`cnt - len`), and extracting it
    must avoid a shift: a `>>>` on the stuck array read `packed[idx]!` forces
    `Nat.shiftRight`/`Nat.div` during the equation compiler's `whnf`, which loops
    on the opaque value — the #2650 hazard. The low byte extracts with `toUInt8`
    (a width truncation, no `Nat.div`), so `unpackLen` stays inert under `whnf`.
    The symbol uses a shift, but it never enters the measure, so its `whnf` is
    never forced during termination checking. -/
@[inline] def packEntry (sym : UInt16) (len : UInt8) : UInt32 :=
  len.toUInt32 ||| (sym.toUInt32 <<< 8)

/-- The symbol field (bits 8–23) of a packed entry. -/
@[inline] def unpackSym (e : UInt32) : UInt16 := (e >>> 8).toUInt16

/-- The codeword-length field (low byte) of a packed entry. Shift-free so it stays
    inert under the `whnf` the well-founded recursions force (see `packEntry`). -/
@[inline] def unpackLen (e : UInt32) : UInt8 := e.toUInt8

/-- A de-boxed fast-decode table: each slot's `(symbol, codeLen)` packed into one
    `UInt32` word (`packEntry`), stored in a single scalar `Array UInt32`. Storing
    `Array (UInt16 × UInt8)` boxes every slot as a heap pair, so each per-symbol
    read pointer-chases through `lean_ctor_get` twice; #2650 split the fields into
    two parallel scalar arrays to de-box; this folds them back into one packed
    word so a per-symbol read is a single `lean_array_fget` plus shifts (`symAt` /
    `lenAt`) touching one tagged-scalar array / one cache line instead of two.

    The only packed field on the well-founded recursions' termination measure is
    the length, and `lenAt` extracts it shift-free (`toUInt8` of the low byte), so
    it stays inert under the `whnf` those recursions force during equation
    compilation — the `Nat.div` loop #2650 warned of (a `>>>` on the stuck
    `packed[idx]!` reducing to `Nat.shiftRight`/`Nat.div`) does not fire. `symAt`
    does shift, but the symbol never enters a measure, so its `whnf` is never
    forced (see `packEntry`). The packed table is kept behind an equivalence to
    the split projections
    (`buildTable_lenAt` / `buildTable_symAt` recover `(tableEntry …).2` /
    `(tableEntry …).1`), so every decode proof transfers. -/
structure DecodeTable where
  packed : Array UInt32

/-- The codeword length of slot `idx`: the low byte of the packed entry. One
    scalar-array read plus a width truncation (no shift — see `packEntry` for why
    the length is the low byte, so this stays inert under the well-founded
    recursions' `whnf`). -/
@[inline] def DecodeTable.lenAt (t : DecodeTable) (idx : Nat) : UInt8 :=
  if h : idx < t.packed.size then unpackLen (t.packed[idx]'h) else 0

/-- The symbol of slot `idx`: bits 8–23 of the packed entry. One scalar-array read
    plus a shift; the symbol never enters a termination measure, so the shift is
    never `whnf`-forced. -/
@[inline] def DecodeTable.symAt (t : DecodeTable) (idx : Nat) : UInt16 :=
  if h : idx < t.packed.size then unpackSym (t.packed[idx]'h) else 0

theorem DecodeTable.lenAt_def (t : DecodeTable) (idx : Nat) :
    t.lenAt idx = unpackLen t.packed[idx]! := by
  unfold DecodeTable.lenAt
  split
  · rw [getElem!_pos t.packed idx ‹_›]
  · rw [getElem!_neg t.packed idx ‹_›]; rfl

theorem DecodeTable.symAt_def (t : DecodeTable) (idx : Nat) :
    t.symAt idx = unpackSym t.packed[idx]! := by
  unfold DecodeTable.symAt
  split
  · rw [getElem!_pos t.packed idx ‹_›]
  · rw [getElem!_neg t.packed idx ‹_›]; rfl

/-- Build the `2^fastBits`-entry decode table for `tree`: slot `i` holds
    `packEntry sym codeLen` for the `(sym, codeLen)` reached by walking `tree` on
    the bits of `i`, stored in a single packed scalar array so each per-symbol read
    is one de-boxed `UInt32` load instead of two reads / a heap-pair pointer-chase.
    Built once per Huffman tree; cheap relative to the symbols decoded with it. -/
def buildTable (tree : HuffTree) : DecodeTable where
  packed := Array.ofFn (n := 2 ^ fastBits) (fun i : Fin (2 ^ fastBits) =>
    packEntry (tableEntry tree i.val).1 (tableEntry tree i.val).2)

/-! ## Canonical O(n) table construction (libdeflate `build_decode_table`)

`buildTable` walks `tree` once per slot — `O(2^fastBits · depth)` with a tree
that itself costs an allocation per block. The libdeflate construction fills the
table directly from the code lengths, with no tree: assign each symbol its
canonical codeword (RFC 1951 §3.2.2, the same `nextCode` recurrence the tree
build uses), then write that symbol's `(sym, len)` into every table slot whose
low `len` bits are the codeword read LSB-first. A length-`len` codeword owns a
contiguous arithmetic progression of `2^(fastBits - len)` slots at stride
`2^len` starting from the bit-reversed codeword, so the whole fill is
`O(num_syms + 2^fastBits)`.

`buildCanonicalLoop` mirrors `HuffTree.insertLoop` step for step — same
`nextCode` threading, same per-symbol code `c` — so the table it fills equals
`buildTable (fromLengthsTree lengths)`: the two constructions assign identical
codewords, and filling the slots of a codeword is the table-side image of
inserting its leaf. The formal equality theorem (`buildTableCanonical_eq`) is the
format-independent core of #2671 and lands in a follow-up — its supporting lemmas
(bit-reversal, the `cwOf`/`bitReverse` slot bridge, the `fillSlots`
characterization) are already in `Zip.Spec.InflateCanonical`, and a differential
conformance test witnesses the equality at runtime across every code-length
regime. The canonical build is not yet on the decode path, so there is no trust
gap; wiring it in waits on the equality proof. -/

/-- Reverse the low `n` bits of `x` (bit `j` of the result is bit `n-1-j` of `x`).
    A length-`len` canonical codeword is written MSB-first into the bitstream, so
    the decoder — which peeks LSB-first — sees `bitReverse code len 0`. -/
def bitReverse (x : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => bitReverse (x / 2) n (acc * 2 + x % 2)

/-- Write `entry` into the `count` slots `base, base + stride, …` of `packed`
    (the slots one length-`len` codeword owns: `stride = 2^len`,
    `count = 2^(fastBits - len)`). Linear in `count`; in-place when `packed` is
    uniquely referenced. -/
def fillSlots (packed : Array UInt32) (base stride count : Nat) (entry : UInt32) :
    Array UInt32 :=
  if count = 0 then packed
  else fillSlots (packed.set! base entry) (base + stride) stride (count - 1) entry
termination_by count

/-- The canonical table-fill loop: for each symbol from `start`, look up its
    canonical code `c = nextCode[len]` (advancing `nextCode[len]`, exactly as
    `HuffTree.insertLoop` does), and — for codes that fit the `fastBits` window —
    fill its slots. Codes longer than `fastBits` advance `nextCode` but fill no
    slot (they reach the table as the sentinel `0`, the long-code fallback), and
    `len = 0` symbols are skipped entirely. -/
def buildCanonicalLoop (lengths : Array UInt8) (nextCode : Array UInt32)
    (start : Nat) (packed : Array UInt32) : Array UInt32 :=
  if h : start < lengths.size then
    let len := lengths[start]
    if hlen : 0 < len.toNat ∧ len.toNat < nextCode.size then
      let c := nextCode[len.toNat]'hlen.2
      let nextCode' := nextCode.set! len.toNat (c + 1)
      if len.toNat ≤ fastBits then
        let base := bitReverse c.toNat len.toNat 0
        let packed' := fillSlots packed base (2 ^ len.toNat)
          (2 ^ (fastBits - len.toNat)) (packEntry start.toUInt16 len)
        buildCanonicalLoop lengths nextCode' (start + 1) packed'
      else
        buildCanonicalLoop lengths nextCode' (start + 1) packed
    else
      buildCanonicalLoop lengths nextCode (start + 1) packed
  else packed
termination_by lengths.size - start

/-- Build the `2^fastBits`-entry decode table directly from the code lengths,
    libdeflate-style — canonical fill, no Huffman tree, no per-slot tree walk.
    Equal to `buildTable (fromLengthsTree lengths)` (formal theorem
    `buildTableCanonical_eq` forthcoming; witnessed at runtime by the
    `InflateTable` canonical conformance test), so once proven it is a drop-in for
    the tree-built table with every decode proof transferring unchanged. -/
def buildTableCanonical (lengths : Array UInt8) (maxBits : Nat := 15) : DecodeTable where
  packed :=
    let lsList := lengths.toList.map UInt8.toNat
    let blCount := Huffman.Spec.countLengths lsList maxBits
    let nextCode : Array UInt32 := (Huffman.Spec.nextCodes blCount maxBits).map (·.toUInt32)
    buildCanonicalLoop lengths nextCode 0 (Array.replicate (2 ^ fastBits) (packEntry 0 0))

/-! ### Fast array-based canonical build inputs

`buildTableCanonical` routes the `nextCode` setup through the proof-oriented
`Huffman.Spec.countLengths` / `nextCodes`, which allocate a `List` (`lengths.toList`)
and run a well-founded recursion — heavier than the per-slot `tableEntry` walk it
was meant to replace. `countLengthsFast` / `nextCodesFast` compute the same arrays
directly over the `Array`, no `List` allocation, as the fast inputs to
`buildCanonicalLoop`. `buildTableCanonicalFast` equals `buildTableCanonical`
(proven by `buildTableCanonicalFast_eq` in `Zip.Spec.InflateCanonical`, and
witnessed by the `InflateTable` conformance test), so it inherits
`buildTableCanonical_eq`. -/

/-- Code-length histogram over the `Array`, no `List` allocation: counts, for each
    length `1..maxBits`, how many symbols carry it (length-0 / out-of-range
    ignored). Fast form of `Huffman.Spec.countLengths`. -/
def countLengthsFast (lengths : Array UInt8) (maxBits : Nat) : Array Nat :=
  go lengths maxBits 0 (Array.replicate (maxBits + 1) 0)
where
  go (lengths : Array UInt8) (maxBits i : Nat) (count : Array Nat) : Array Nat :=
    if h : i < lengths.size then
      let ln := lengths[i].toNat
      let count := if 0 < ln ∧ ln ≤ maxBits then count.set! ln (count[ln]! + 1) else count
      go lengths maxBits (i + 1) count
    else count
  termination_by lengths.size - i

/-- Kraft sum `∑_{len=0}^{maxBits} count[len] · 2^(maxBits − len)` over the
    per-length histogram, by an `O(maxBits)` tail loop with **no allocation** —
    `count` is the same array `buildTableCanonicalFast` already builds. (The `len=0`
    term is zero for a `countLengthsFast` histogram, which never sets index 0, so it
    contributes nothing while keeping the recurrence aligned with the spec's
    `kraftSumFrom` from `0`.) The Kraft check `validateLengths` runs is then this
    sum against `2^maxBits`, replacing the per-block `lengths.toList`/`filter`
    `List` allocation `fromLengths` uses. -/
def kraftSumFast (count : Array Nat) (maxBits : Nat) : Nat :=
  go count maxBits 0 0
where
  go (count : Array Nat) (maxBits b acc : Nat) : Nat :=
    if h : b ≤ maxBits then
      go count maxBits (b + 1) (acc + count[b]! * 2 ^ (maxBits - b))
    else acc
  termination_by maxBits + 1 - b

/-- The code-length validity check that `fromLengths` performs, factored out so a
    decoder that builds no tree (the canonical tree-free path) can reject exactly
    the malformed length sets `fromLengths` rejects, with the same error messages:
    `"Inflate: code length exceeds maximum"` for any length `> maxBits`, and
    `"Inflate: oversubscribed Huffman code"` when the Kraft sum overflows. The Kraft
    sum is computed from the per-length `count` histogram (`countLengthsFast` —
    the same array the canonical table build needs) via the allocation-free
    `kraftSumFast`, rather than the per-block `List` (`lengths.toList`/`filter`)
    `fromLengths` allocates; the over-bound check is a plain `Array.any`. No tree is
    built. `fromLengths = (validateLengths …).map (fun _ => fromLengthsTree …)`
    (`Zip.Spec.InflateTreeFreeCorrect.fromLengths_eq_validate`). -/
def validateLengths (lengths : Array UInt8) (maxBits : Nat := 15) :
    Except String Unit :=
  if lengths.any (fun l => l.toNat > maxBits) then
    .error "Inflate: code length exceeds maximum"
  else if kraftSumFast (countLengthsFast lengths maxBits) maxBits > 2 ^ maxBits then
    .error "Inflate: oversubscribed Huffman code"
  else
    .ok ()

/-- First canonical code per length (RFC 1951 §3.2.2 step 2), as a `UInt32` array
    computed by a direct `1..maxBits` loop — fast form of
    `(Huffman.Spec.nextCodes count maxBits).map (·.toUInt32)`. -/
def nextCodesFast (count : Array Nat) (maxBits : Nat) : Array UInt32 :=
  go count maxBits 1 0 (Array.replicate (maxBits + 1) 0)
where
  go (count : Array Nat) (maxBits bits code : Nat) (nc : Array UInt32) : Array UInt32 :=
    if h : bits ≤ maxBits then
      let code := (code + count[bits - 1]!) * 2
      go count maxBits (bits + 1) code (nc.set! bits code.toUInt32)
    else nc
  termination_by maxBits + 1 - bits

/-- Build the canonical decode table with the fast array-based `nextCode` setup
    (`countLengthsFast` / `nextCodesFast`), avoiding the `List` allocation and
    well-founded recursion of `buildTableCanonical`'s spec-function inputs. Equal
    to `buildTableCanonical` — same `buildCanonicalLoop`, same `nextCode` array —
    so it is a drop-in carrying `buildTableCanonical_eq` once the array/spec
    equality is proven (witnessed now by the `InflateTable` conformance test). -/
def buildTableCanonicalFast (lengths : Array UInt8) (maxBits : Nat := 15) : DecodeTable where
  packed :=
    let count := countLengthsFast lengths maxBits
    let nextCode := nextCodesFast count maxBits
    buildCanonicalLoop lengths nextCode 0 (Array.replicate (2 ^ fastBits) (packEntry 0 0))

/-- `buildTableCanonicalFast` taking a precomputed length histogram, so a per-block
    decoder building both the fast table and the long-code structures can share a
    single `countLengthsFast` pass over the length vector. Definitionally equal to
    `buildTableCanonicalFast lengths maxBits` when `count = countLengthsFast lengths
    maxBits` (`buildTableCanonicalFastWithCount_eq`). -/
def buildTableCanonicalFastWithCount (lengths : Array UInt8) (count : Array Nat)
    (maxBits : Nat := 15) : DecodeTable where
  packed :=
    let nextCode := nextCodesFast count maxBits
    buildCanonicalLoop lengths nextCode 0 (Array.replicate (2 ^ fastBits) (packEntry 0 0))

/-- Bits remaining in the reader from its current `(pos, bitOff)`. -/
def bitsAvail (br : BitReader) : Nat :=
  if br.pos ≥ br.data.size then 0 else (br.data.size - br.pos) * 8 - br.bitOff

/-- Peek the next `fastBits` bits at `(pos, bitOff)`, LSB-first, without
    consuming. Reads 3 bytes: a `≤ 7`-bit `bitOff` plus the 11-bit window spans
    bits `0 … 17`, so three bytes (bits `0 … 23`) always cover it. Bytes past the
    end of the stream read as zero; the caller uses `bitsAvail` to decide whether
    the looked-up code actually fits. -/
def peekFast (br : BitReader) : UInt32 :=
  let b0 : UInt32 := if h : br.pos < br.data.size then (br.data[br.pos]'h).toUInt32 else 0
  let b1 : UInt32 := if h : br.pos + 1 < br.data.size then (br.data[br.pos + 1]'h).toUInt32 else 0
  let b2 : UInt32 := if h : br.pos + 2 < br.data.size then (br.data[br.pos + 2]'h).toUInt32 else 0
  ((b0 ||| (b1 <<< 8) ||| (b2 <<< 16)) >>> br.bitOff.toUInt32) &&& 0x7FF

/-- Table-driven single-symbol decode. Peeks `fastBits` bits, reads the
    `(symbol, codeLen)` from `table`, and consumes `codeLen` bits in one step.
    Falls back to the canonical `decode` tree walk for long codes (sentinel
    `codeLen = 0`) and when fewer than `codeLen` bits remain. Proven equal to
    `decode` when `table = buildTable tree` (`Zip.Spec.InflateTable`). -/
def decodeWithTable (tree : HuffTree) (table : DecodeTable)
    (br : BitReader) : Except String (UInt16 × BitReader) :=
  -- `bitOff ≥ 8` is unreachable for a well-formed reader (every `readBit`
  -- leaves `bitOff < 8`); the guard makes the equality with `decode`
  -- unconditional, so the proof transfer needs no side conditions.
  if br.bitOff ≥ 8 then tree.decode br
  else
    let idx := (peekFast br).toNat
    let len := (table.lenAt idx).toNat
    if len == 0 || len > bitsAvail br then
      tree.decode br
    else
      let total := br.bitOff + len
      .ok (table.symAt idx, { br with pos := br.pos + total / 8, bitOff := total % 8 })

end HuffTree

namespace Inflate

-- RFC 1951 §3.2.5: Fixed Huffman code lengths for lit/length (0–287)
def fixedLitLengths : Array UInt8 :=
  .replicate 144 8 ++ .replicate 112 9 ++
  .replicate 24 7 ++ .replicate 8 8

-- RFC 1951 §3.2.5: Fixed Huffman code lengths for distance (0–31)
def fixedDistLengths : Array UInt8 := .replicate 32 (5 : UInt8)

-- Length base values for codes 257–285 (RFC 1951 §3.2.5)
def lengthBase : Array UInt16 := #[
  3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31,
  35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258
]

-- Extra bits for length codes 257–285
def lengthExtra : Array UInt8 := #[
  0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2,
  3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0
]

@[simp] theorem lengthBase_size : lengthBase.size = 29 := by decide
@[simp] theorem lengthExtra_size : lengthExtra.size = 29 := by decide

-- Distance base values for codes 0–29
def distBase : Array UInt16 := #[
  1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193,
  257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289,
  16385, 24577
]

-- Extra bits for distance codes 0–29
def distExtra : Array UInt8 := #[
  0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6,
  7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13
]

@[simp] theorem distBase_size : distBase.size = 30 := by decide
@[simp] theorem distExtra_size : distExtra.size = 30 := by decide

/-- The per-byte back-reference copy worker: copy `length` bytes from `buf`
    starting at `start`, repeating every `distance` bytes (LZ77 copy with
    wrap-around). Defined as explicit recursion for proof tractability; this is
    the reference semantics that `copyLoop` dispatches to. -/
def copyLoopGo (buf : ByteArray) (start distance : Nat)
    (k length : Nat)
    (hd_pos : distance > 0 := by omega) (hsd : start + distance ≤ buf.size := by omega) : ByteArray :=
  if k < length then
    have hidx : start + (k % distance) < buf.size := by
      have := Nat.mod_lt k hd_pos; omega
    copyLoopGo (buf.push buf[start + (k % distance)]) start distance (k + 1) length
      hd_pos (by simp [ByteArray.size_push]; omega)
  else buf
termination_by length - k

/-- Copy `length` bytes from `buf` starting at `start`, repeating every
    `distance` bytes (LZ77 back-reference copy).

    For the common **non-overlapping** back-reference (`k = 0 ∧ length ≤ distance`)
    every index `start + (k % distance)` is just `start + k`, so the whole copy is
    the contiguous slice `[start, start + length)`, appended in a single pass by
    `ByteArray.copyWithin` (one `memcpy`, no intermediate allocation — its
    reference body is exactly `buf ++ buf.extract start (start + length)`) instead
    of `length` per-byte `push`es / bounds-checks / modular indices. For an
    **overlapping** back-reference (`k = 0 ∧ length > distance`,
    the RLE case) the copy is the periodic extension of the `distance`-byte
    window, appended in a single allocation-free pass by `ByteArray.extendWithin`
    (its reference body is exactly the `fillDouble`-based expression) instead of
    `length` per-byte `push`es. A partial copy (`k ≠ 0`, never produced by the
    decoders) falls back to the per-byte `copyLoopGo`. All three are proven equal
    to `copyLoopGo` via `copyLoop_eq_ofFn`, so every decode correctness proof is
    unaffected. -/
def copyLoop (buf : ByteArray) (start distance : Nat)
    (k length : Nat)
    (hd_pos : distance > 0 := by omega) (hsd : start + distance ≤ buf.size := by omega) : ByteArray :=
  if k = 0 ∧ length ≤ distance then
    buf.copyWithin start length
  else if k = 0 then
    buf.extendWithin start distance length
  else
    copyLoopGo buf start distance k length hd_pos hsd

-- Code length alphabet order for dynamic Huffman (RFC 1951 §3.2.7)
def codeLengthOrder : Array Nat := #[
  16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15
]

@[simp] theorem codeLengthOrder_size : codeLengthOrder.size = 19 := by decide

/-- Fill `count` consecutive entries starting at `idx` with `val`,
    stopping when `idx ≥ bound`. Returns updated array and new index. -/
def fillEntries (arr : Array UInt8) (idx count bound : Nat) (val : UInt8) :
    Array UInt8 × Nat :=
  if count = 0 ∨ idx ≥ bound then (arr, idx)
  else fillEntries (arr.set! idx val) (idx + 1) (count - 1) bound val
termination_by count

private theorem fillEntries_snd_eq (arr : Array UInt8) (idx count bound : Nat) (val : UInt8)
    (h : idx + count ≤ bound) :
    (fillEntries arr idx count bound val).snd = idx + count := by
  induction count generalizing arr idx with
  | zero => simp [fillEntries]
  | succ n ih =>
    unfold fillEntries
    simp only [Nat.succ_ne_zero, false_or, show ¬(idx ≥ bound) from by omega,
               ↓reduceIte, Nat.add_sub_cancel]
    rw [ih (arr.set! idx val) (idx + 1) (by omega)]; omega

/-- Read code length code lengths: 3 bits each at permuted positions.
    Defined as explicit recursion for proof tractability. -/
def readCLCodeLengths (br : BitReader) (clLengths : Array UInt8)
    (i numCodeLen : Nat) : Except String (Array UInt8 × BitReader) :=
  if i < numCodeLen then do
    if h_i : i < codeLengthOrder.size then
      let (v, br) ← br.readBits 3
      readCLCodeLengths br (clLengths.set! (codeLengthOrder[i]) v.toUInt8) (i + 1) numCodeLen
    else
      throw "Inflate: code length index out of bounds"
  else
    .ok (clLengths, br)
termination_by numCodeLen - i

/-- Decode code lengths using the CL Huffman tree (RFC 1951 §3.2.7).
    Processes symbols: 0–15 (literal length), 16 (repeat previous),
    17 (repeat 0, short), 18 (repeat 0, long).
    Defined as explicit recursion for proof tractability. -/
def decodeCLSymbols (clTree : HuffTree) (br : BitReader)
    (codeLengths : Array UInt8) (idx totalCodes : Nat)
    : Except String (Array UInt8 × BitReader) :=
  if idx ≥ totalCodes then .ok (codeLengths, br)
  else do
    let (sym, br) ← clTree.decode br
    if sym < 16 then
      decodeCLSymbols clTree br (codeLengths.set! idx sym.toUInt8) (idx + 1) totalCodes
    else if sym == 16 then
      if idx == 0 then throw "Inflate: repeat code at start"
      if h_cl : idx - 1 < codeLengths.size then do
        let (rep, br) ← br.readBits 2
        let prev := codeLengths[idx - 1]
        let count := rep.toNat + 3
        if idx + count > totalCodes then throw "Inflate: repeat code exceeds total"
        decodeCLSymbols clTree br (fillEntries codeLengths idx count totalCodes prev).1
          (idx + count) totalCodes
      else throw "Inflate: repeat code index out of bounds"
    else if sym == 17 then
      let (rep, br) ← br.readBits 3
      let count := rep.toNat + 3
      if idx + count > totalCodes then throw "Inflate: repeat code exceeds total"
      decodeCLSymbols clTree br (fillEntries codeLengths idx count totalCodes 0).1
        (idx + count) totalCodes
    else if sym == 18 then
      let (rep, br) ← br.readBits 7
      let count := rep.toNat + 11
      if idx + count > totalCodes then throw "Inflate: repeat code exceeds total"
      decodeCLSymbols clTree br (fillEntries codeLengths idx count totalCodes 0).1
        (idx + count) totalCodes
    else
      throw s!"Inflate: invalid code length symbol {sym}"
termination_by totalCodes - idx
decreasing_by all_goals omega

/-- Decode dynamic Huffman trees from the bitstream (RFC 1951 §3.2.7). -/
def decodeDynamicTrees (br : BitReader) :
    Except String (HuffTree × HuffTree × BitReader) := do
  let (hlit, br) ← br.readBits 5
  let (hdist, br) ← br.readBits 5
  let (hclen, br) ← br.readBits 4
  let numLitLen := hlit.toNat + 257
  let numDist := hdist.toNat + 1
  let numCodeLen := hclen.toNat + 4
  let (clLengths, br) ← readCLCodeLengths br (.replicate 19 0) 0 numCodeLen
  let clTree ← HuffTree.fromLengths clLengths 7
  let totalCodes := numLitLen + numDist
  let (codeLengths, br) ← decodeCLSymbols clTree br (.replicate totalCodes 0)
    0 totalCodes
  let litLenLengths := codeLengths.extract 0 numLitLen
  let distLengths := codeLengths.extract numLitLen totalCodes
  let litTree ← HuffTree.fromLengths litLenLengths
  let distTree ← HuffTree.fromLengths distLengths
  return (litTree, distTree, br)

/-- Decode a stored (uncompressed) block. -/
protected def decodeStored (br : BitReader) (output : ByteArray)
    (maxOutputSize : Nat) : Except String (ByteArray × BitReader) := do
  let (len, br) ← br.readUInt16LE
  let (nlen, br) ← br.readUInt16LE
  if len ^^^ nlen != 0xFFFF then
    throw "Inflate: stored block length check failed"
  if output.size + len.toNat > maxOutputSize then
    throw "Inflate: output exceeds maximum size"
  let (bytes, br) ← br.readBytes len.toNat
  return (output ++ bytes, br)

/-- Decode a Huffman-coded block (fixed or dynamic).
    Uses well-founded recursion on the remaining bits in the stream. -/
protected def decodeHuffman (br : BitReader) (output : ByteArray)
    (litTree distTree : HuffTree) (maxOutputSize : Nat)
    : Except String (ByteArray × BitReader) :=
  go br.data.size br output
where
  go (dataSize : Nat) (br : BitReader) (output : ByteArray)
      : Except String (ByteArray × BitReader) := do
    let (sym, br₁) ← litTree.decode br
    if sym < 256 then
      if output.size ≥ maxOutputSize then
        throw "Inflate: output exceeds maximum size"
      -- Guard: bit position must advance for WF termination
      if _h₁ : br₁.bitPos ≤ br.bitPos then
        throw "Inflate: no progress in Huffman decode"
      else if _h₂ : dataSize * 8 < br₁.bitPos then
        throw "Inflate: bit position out of range"
      else
        go dataSize br₁ (output.push sym.toUInt8)
    else if sym == 256 then
      .ok (output, br₁)
    else
      -- Length code 257–285
      let idx := sym.toNat - 257
      if h : idx ≥ lengthBase.size then
        throw s!"Inflate: invalid length code {sym}"
      else
      let base := lengthBase[idx]
      let extra := lengthExtra[idx]'(by simp [lengthExtra_size, lengthBase_size] at h ⊢; omega)
      let (extraBits, br₂) ← br₁.readBits extra.toNat
      let length := base.toNat + extraBits.toNat
      -- Distance code
      let (distSym, br₃) ← distTree.decode br₂
      let dIdx := distSym.toNat
      if h : dIdx ≥ distBase.size then
        throw s!"Inflate: invalid distance code {distSym}"
      else
      let dBase := distBase[dIdx]
      let dExtra := distExtra[dIdx]'(by simp [distExtra_size, distBase_size] at h ⊢; omega)
      let (dExtraBits, br₄) ← br₃.readBits dExtra.toNat
      let distance := dBase.toNat + dExtraBits.toNat
      -- Copy from output buffer (LZ77 back-reference)
      if hd0 : distance = 0 then
        throw s!"Inflate: zero back-reference distance"
      else if hds : distance > output.size then
        throw s!"Inflate: distance {distance} exceeds output size {output.size}"
      else if output.size + length > maxOutputSize then
        throw "Inflate: output exceeds maximum size"
      else
      let start := output.size - distance
      let out := copyLoop output start distance 0 length
        (by omega) (by omega)
      -- Guard: bit position must advance for WF termination
      if _h₁ : br₄.bitPos ≤ br.bitPos then
        throw "Inflate: no progress in Huffman decode"
      else if _h₂ : dataSize * 8 < br₄.bitPos then
        throw "Inflate: bit position out of range"
      else
        go dataSize br₄ out
  termination_by dataSize * 8 - br.bitPos
  decreasing_by all_goals omega

/-- Table-driven variant of `decodeHuffman`: identical to it except the two
    Huffman symbol decodes go through `decodeWithTable` (fast-bits lookup table)
    instead of the bit-by-bit `HuffTree.decode` walk. The literal/length and
    distance tables are built once, up front, then reused for every symbol in
    the block. Proven equal to `decodeHuffman` symbol-by-symbol through
    `HuffTree.decodeWithTable_eq` (see `decodeHuffmanFastBR_eq`).

    This is the **BitReader reference** decoder. The default `decodeHuffmanFast`
    (below) delegates to the faster wide-buffer `InflateBuf.decodeHuffmanFastBuf`,
    which is proven equal to *this* (`decodeHuffmanFastBuf_eq`); composing the two
    equalities gives `decodeHuffmanFast = decodeHuffman`, so the bit-by-bit walk
    stays the canonical spec and every inflate correctness proof transfers. -/
protected def decodeHuffmanFastBR (br : BitReader) (output : ByteArray)
    (litTree distTree : HuffTree) (maxOutputSize : Nat)
    : Except String (ByteArray × BitReader) :=
  go litTree.buildTable distTree.buildTable br.data.size br output
where
  go (litTable distTable : HuffTree.DecodeTable)
      (dataSize : Nat) (br : BitReader) (output : ByteArray)
      : Except String (ByteArray × BitReader) := do
    let (sym, br₁) ← litTree.decodeWithTable litTable br
    if sym < 256 then
      if output.size ≥ maxOutputSize then
        throw "Inflate: output exceeds maximum size"
      else if _h₁ : br₁.bitPos ≤ br.bitPos then
        throw "Inflate: no progress in Huffman decode"
      else if _h₂ : dataSize * 8 < br₁.bitPos then
        throw "Inflate: bit position out of range"
      else
        go litTable distTable dataSize br₁ (output.push sym.toUInt8)
    else if sym == 256 then
      .ok (output, br₁)
    else
      let idx := sym.toNat - 257
      if h : idx ≥ lengthBase.size then
        throw s!"Inflate: invalid length code {sym}"
      else
      let base := lengthBase[idx]
      let extra := lengthExtra[idx]'(by simp [lengthExtra_size, lengthBase_size] at h ⊢; omega)
      let (extraBits, br₂) ← readBitsFast br₁ extra.toNat
      let length := base.toNat + extraBits.toNat
      let (distSym, br₃) ← distTree.decodeWithTable distTable br₂
      let dIdx := distSym.toNat
      if h : dIdx ≥ distBase.size then
        throw s!"Inflate: invalid distance code {distSym}"
      else
      let dBase := distBase[dIdx]
      let dExtra := distExtra[dIdx]'(by simp [distExtra_size, distBase_size] at h ⊢; omega)
      let (dExtraBits, br₄) ← readBitsFast br₃ dExtra.toNat
      let distance := dBase.toNat + dExtraBits.toNat
      if hd0 : distance = 0 then
        throw s!"Inflate: zero back-reference distance"
      else if hds : distance > output.size then
        throw s!"Inflate: distance {distance} exceeds output size {output.size}"
      else if output.size + length > maxOutputSize then
        throw "Inflate: output exceeds maximum size"
      else
      let start := output.size - distance
      let out := copyLoop output start distance 0 length
        (by omega) (by omega)
      if _h₁ : br₄.bitPos ≤ br.bitPos then
        throw "Inflate: no progress in Huffman decode"
      else if _h₂ : dataSize * 8 < br₄.bitPos then
        throw "Inflate: bit position out of range"
      else
        go litTable distTable dataSize br₄ out
  termination_by dataSize * 8 - br.bitPos
  decreasing_by all_goals omega

end Inflate

/-!
## Wide-buffer Huffman decoder primitives (Track D, #2501)

Thread the bit cursor as unboxed scalars `(pos, bitBuf : UInt64, cnt)` — plus a
`bitpos` measure for termination — through the whole Huffman symbol loop,
refilling up to 57 bits at a time and consuming by shift, instead of allocating
a fresh `BitReader` per field read. `Zip.Spec.InflateBufCorrect` proves
`decodeHuffmanFastBuf` equal to the BitReader reference `Inflate.decodeHuffmanFastBR`
(for depth-≤15 trees and a well-formed reader), so the default `inflateLoop` adopts
it with no trust gap (no `@[extern]`, no `@[implemented_by]`).
-/
namespace InflateBuf
open ZipCommon (BitReader)

/-! ## USize-addressability bridge lemmas (#2652)

The production symbol loop `goFusedPU` threads the byte cursor `pos` and the
bit count `cnt` as raw `USize` words. These two lemmas bridge `USize` indexing
and round-tripping back to `Nat` `getElem`, so the unboxed loop is proven equal
to the boxed-`Nat` loop `goFusedP` (`goFusedPU_eq`). -/

/-- A `Nat` below `USize.size` round-trips through `USize` unchanged. -/
theorem toUSize_toNat_of_lt {n : Nat} (h : n < USize.size) : n.toUSize.toNat = n := by
  simp only [Nat.toUSize_eq]; exact USize.toNat_ofNat_of_lt' h

/-- `ByteArray.uget` at `i` is `getElem` at `i.toNat` (definitional). -/
theorem uget_eq_getElem (data : ByteArray) (i : USize) (h : i.toNat < data.size) :
    data.uget i h = data[i.toNat]'h := rfl

/-- `ByteArray.uget` agrees with the panicking `getElem!` in bounds. -/
theorem uget_eq_getElem! (data : ByteArray) (i : USize) (h : i.toNat < data.size) :
    data.uget i h = data[i.toNat]! := by
  rw [uget_eq_getElem]; exact (getElem!_pos data i.toNat h).symm

/-- The `USize→UInt64` conversion factors through `Nat` (both keep `toNat`). -/
theorem usize_toUInt64_toNat (c : USize) : c.toUInt64 = c.toNat.toUInt64 := by
  apply UInt64.toNat.inj
  rw [USize.toNat_toUInt64, Nat.toUInt64_eq, UInt64.toNat_ofNat']
  exact (Nat.mod_eq_of_lt c.toNat_lt).symm

/-- The fused refill guard read in `USize` matches the `Nat` guard once the buffer
    is `USize`-addressable. -/
theorem refillGuard_usize (data : ByteArray) (pos cnt : USize) (hsz : data.size < USize.size) :
    (cnt ≤ (56 : USize) ∧ pos < data.size.toUSize)
      ↔ (cnt.toNat ≤ 56 ∧ pos.toNat < data.size) := by
  rw [USize.le_iff_toNat_le, USize.lt_iff_toNat_lt, toUSize_toNat_of_lt hsz,
      USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)]

/-- The inline-literal guard read in `USize` matches the `Nat` guard (the length
    field round-trips since it is a `UInt8`). -/
theorem litGuard_usize (table : HuffTree.DecodeTable) (bitBuf : UInt64) (cnt : USize) :
    ((table.lenAt (bitBuf &&& 0x7FF).toNat).toNat ≠ 0
        ∧ ((table.lenAt (bitBuf &&& 0x7FF).toNat).toNat).toUSize ≤ cnt
        ∧ table.symAt (bitBuf &&& 0x7FF).toNat < 256)
      ↔ ((table.lenAt (bitBuf &&& 0x7FF).toNat).toNat ≠ 0
        ∧ (table.lenAt (bitBuf &&& 0x7FF).toNat).toNat ≤ cnt.toNat
        ∧ table.symAt (bitBuf &&& 0x7FF).toNat < 256) := by
  rw [USize.le_iff_toNat_le, toUSize_toNat_of_lt (UInt8.toNat_lt_usizeSize _)]

/-- Load whole bytes into the high end of `bitBuf` until it holds > 56 bits or
    the input is exhausted. Preserves the consumed bit position `pos*8 - cnt`. -/
@[specialize] def refill (data : ByteArray) (pos : Nat) (bitBuf : UInt64) (cnt : Nat) :
    Nat × UInt64 × Nat :=
  if h : cnt ≤ 56 ∧ pos < data.size then
    refill data (pos + 1) (bitBuf ||| ((data[pos]'h.2).toUInt64 <<< cnt.toUInt64)) (cnt + 8)
  else (pos, bitBuf, cnt)
termination_by data.size - pos
decreasing_by simp_wf; omega

/-- Bit-by-bit tree walk over the buffer (fallback for codes longer than the
    11-bit table or near end-of-input). Mirrors `HuffTree.decode.go` exactly
    (same `depth > 20` guard, same error strings), so it is provably equal;
    `depth` is the tree-walk depth. Returns the symbol, the remaining buffer,
    and the number of bits consumed. -/
def walkTree (t : HuffTree) (bitBuf : UInt64) (cnt depth : Nat) :
    Except String (UInt16 × UInt64 × Nat × Nat) :=
  match t with
  | .leaf s => .ok (s, bitBuf, cnt, 0)
  | .empty => .error "Inflate: invalid Huffman code"
  | .node z o =>
    if depth > 20 then .error "Inflate: Huffman decode exceeded max depth"
    else if cnt = 0 then .error "BitReader: unexpected end of input"
    else
      match walkTree (if bitBuf &&& 1 == 0 then z else o) (bitBuf >>> 1) (cnt - 1) (depth + 1) with
      | .error e => .error e
      | .ok (s, bb, c, used) => .ok (s, bb, c, used + 1)

/-- Decode one Huffman symbol from the (refilled) buffer via the 11-bit table,
    falling back to the tree walk for long codes / near EOF. Returns the symbol,
    remaining buffer state, and bits consumed. -/
@[inline] def decodeSym (tree : HuffTree) (table : HuffTree.DecodeTable)
    (bitBuf : UInt64) (cnt : Nat) : Except String (UInt16 × UInt64 × Nat × Nat) :=
  let idx := (bitBuf &&& 0x7FF).toNat
  let len := (table.lenAt idx).toNat
  if len == 0 || len > cnt then walkTree tree bitBuf cnt 0
  else .ok (table.symAt idx, bitBuf >>> len.toUInt64, cnt - len, len)

/-- Read `n` bits LSB-first from the buffer without refilling. Errors (like
    `readBitsFast`) when the buffer holds fewer than `n` bits — for a refilled
    buffer this only fires at true end-of-input on a truncated stream. -/
@[inline] def takeBits (bitBuf : UInt64) (cnt n : Nat) : Except String (Nat × UInt64 × Nat) :=
  if n > cnt then .error "BitReader: unexpected end of input"
  else
    let v := (bitBuf &&& ((1 <<< n.toUInt64) - 1)).toNat
    .ok (v, bitBuf >>> n.toUInt64, cnt - n)

/-- `takeBits` never increases the bit count. -/
theorem takeBits_le (bitBuf : UInt64) (cnt n : Nat) {v : Nat} {bb : UInt64} {c : Nat}
    (h : takeBits bitBuf cnt n = .ok (v, bb, c)) : c ≤ cnt := by
  unfold takeBits at h
  split at h
  · exact absurd h (by simp)
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega

set_option maxRecDepth 4096 in
/-- Wide-buffer Huffman symbol loop (mirrors `Inflate.decodeHuffmanFastBR.go`).
    `bitpos` is the stream bit position (`= pos*8 - cnt` under the buffer
    invariant); it carries the well-founded measure and the progress guards. -/
def go (litTable distTable : HuffTree.DecodeTable)
    (data : ByteArray) (litTree distTree : HuffTree) (maxOut dataSize : Nat)
    (pos : Nat) (bitBuf : UInt64) (cnt bitpos : Nat) (output : ByteArray) :
    Except String (ByteArray × Nat × UInt64 × Nat × Nat) := do
  -- One refill covers a full worst case: lit(15)+lenExtra(13)+dist(15)+distExtra(13)=56.
  let (pos, bitBuf, cnt) := refill data pos bitBuf cnt
  -- `cnt0` = bits available after refill; consumed bits = `cnt0 - cnt` (plain Nats,
  -- so the termination measure carries no array-access atoms).
  let cnt0 := cnt
  match decodeSym litTree litTable bitBuf cnt with
  | .error e => .error e
  | .ok (sym, bitBuf, cnt, _used) =>
    if sym < 256 then
      if output.size ≥ maxOut then throw "Inflate: output exceeds maximum size"
      else if _h₁ : bitpos + (cnt0 - cnt) ≤ bitpos then throw "Inflate: no progress in Huffman decode"
      else if _h₂ : dataSize * 8 < bitpos + (cnt0 - cnt) then throw "Inflate: bit position out of range"
      else
        go litTable distTable data litTree distTree maxOut dataSize pos bitBuf cnt (bitpos + (cnt0 - cnt)) (output.push sym.toUInt8)
    else if sym == 256 then
      .ok (output, pos, bitBuf, cnt, bitpos + (cnt0 - cnt))
    else
      let idx := sym.toNat - 257
      if h : idx ≥ Inflate.lengthBase.size then throw s!"Inflate: invalid length code {sym}"
      else
        let base := Inflate.lengthBase[idx]
        let extra := Inflate.lengthExtra[idx]'(by simp [Inflate.lengthExtra_size, Inflate.lengthBase_size] at h ⊢; omega)
        let (extraBits, bitBuf, cnt) ← takeBits bitBuf cnt extra.toNat
        let length := base.toNat + extraBits
        match decodeSym distTree distTable bitBuf cnt with
        | .error e => .error e
        | .ok (distSym, bitBuf, cnt, _dused) =>
          let dIdx := distSym.toNat
          if h : dIdx ≥ Inflate.distBase.size then throw s!"Inflate: invalid distance code {distSym}"
          else
            let dBase := Inflate.distBase[dIdx]
            let dExtra := Inflate.distExtra[dIdx]'(by simp [Inflate.distExtra_size, Inflate.distBase_size] at h ⊢; omega)
            let (dExtraBits, bitBuf, cnt) ← takeBits bitBuf cnt dExtra.toNat
            let distance := dBase.toNat + dExtraBits
            if h0 : distance = 0 then throw s!"Inflate: zero back-reference distance"
            else if hds : distance > output.size then
              throw s!"Inflate: distance {distance} exceeds output size {output.size}"
            else if output.size + length > maxOut then throw "Inflate: output exceeds maximum size"
            else if _h₁ : bitpos + (cnt0 - cnt) ≤ bitpos then throw "Inflate: no progress in Huffman decode"
            else if _h₂ : dataSize * 8 < bitpos + (cnt0 - cnt) then throw "Inflate: bit position out of range"
            else
              let out := Inflate.copyLoop output (output.size - distance) distance 0 length
                (by omega) (by omega)
              go litTable distTable data litTree distTree maxOut dataSize pos bitBuf cnt (bitpos + (cnt0 - cnt)) out
termination_by dataSize * 8 - bitpos
decreasing_by all_goals omega

set_option maxRecDepth 4096 in
/-- Fused-refill variant of `go`: the `refill` byte-loading loop is unrolled
    into the recursion (the `cnt ≤ 56 ∧ pos < data.size` branch loads one byte
    and self-recurses), so the whole decoder compiles to a single tail-recursive
    `goto` loop with `bitBuf` in a register and **no per-token `refill` tuple**.
    Decode branches are byte-for-byte the bodies of `go` (same guards, same
    errors), so `goFused = go` (`Zip.Spec.InflateBufCorrect.goFused_eq_go`); it
    is the production hot path. `(dataSize*8 - bitpos, data.size - pos)`
    decreases lexicographically: refill steps shrink `data.size - pos` (first
    component fixed since `bitpos` is unchanged), decode steps shrink
    `dataSize*8 - bitpos` via the progress guards. See #2637. -/
def goFused (litTable distTable : HuffTree.DecodeTable)
    (data : ByteArray) (litTree distTree : HuffTree) (maxOut dataSize : Nat)
    (pos : Nat) (bitBuf : UInt64) (cnt bitpos : Nat) (output : ByteArray) :
    Except String (ByteArray × Nat × UInt64 × Nat × Nat) := do
  if hrc : cnt ≤ 56 ∧ pos < data.size then
    goFused litTable distTable data litTree distTree maxOut dataSize
      (pos + 1) (bitBuf ||| ((data[pos]'hrc.2).toUInt64 <<< cnt.toUInt64)) (cnt + 8) bitpos output
  else
  let cnt0 := cnt
  match decodeSym litTree litTable bitBuf cnt with
  | .error e => .error e
  | .ok (sym, bitBuf, cnt, _used) =>
    if sym < 256 then
      if output.size ≥ maxOut then throw "Inflate: output exceeds maximum size"
      else if _h₁ : bitpos + (cnt0 - cnt) ≤ bitpos then throw "Inflate: no progress in Huffman decode"
      else if _h₂ : dataSize * 8 < bitpos + (cnt0 - cnt) then throw "Inflate: bit position out of range"
      else
        goFused litTable distTable data litTree distTree maxOut dataSize pos bitBuf cnt (bitpos + (cnt0 - cnt)) (output.push sym.toUInt8)
    else if sym == 256 then
      .ok (output, pos, bitBuf, cnt, bitpos + (cnt0 - cnt))
    else
      let idx := sym.toNat - 257
      if h : idx ≥ Inflate.lengthBase.size then throw s!"Inflate: invalid length code {sym}"
      else
        let base := Inflate.lengthBase[idx]
        let extra := Inflate.lengthExtra[idx]'(by simp [Inflate.lengthExtra_size, Inflate.lengthBase_size] at h ⊢; omega)
        let (extraBits, bitBuf, cnt) ← takeBits bitBuf cnt extra.toNat
        let length := base.toNat + extraBits
        match decodeSym distTree distTable bitBuf cnt with
        | .error e => .error e
        | .ok (distSym, bitBuf, cnt, _dused) =>
          let dIdx := distSym.toNat
          if h : dIdx ≥ Inflate.distBase.size then throw s!"Inflate: invalid distance code {distSym}"
          else
            let dBase := Inflate.distBase[dIdx]
            let dExtra := Inflate.distExtra[dIdx]'(by simp [Inflate.distExtra_size, Inflate.distBase_size] at h ⊢; omega)
            let (dExtraBits, bitBuf, cnt) ← takeBits bitBuf cnt dExtra.toNat
            let distance := dBase.toNat + dExtraBits
            if h0 : distance = 0 then throw s!"Inflate: zero back-reference distance"
            else if hds : distance > output.size then
              throw s!"Inflate: distance {distance} exceeds output size {output.size}"
            else if output.size + length > maxOut then throw "Inflate: output exceeds maximum size"
            else if _h₁ : bitpos + (cnt0 - cnt) ≤ bitpos then throw "Inflate: no progress in Huffman decode"
            else if _h₂ : dataSize * 8 < bitpos + (cnt0 - cnt) then throw "Inflate: bit position out of range"
            else
              let out := Inflate.copyLoop output (output.size - distance) distance 0 length
                (by omega) (by omega)
              goFused litTable distTable data litTree distTree maxOut dataSize pos bitBuf cnt (bitpos + (cnt0 - cnt)) out
termination_by (dataSize * 8 - bitpos, data.size - pos)
decreasing_by
  · exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.left _ _ (by omega)

/-! ## EXPERIMENT: provable-shape guard-light decoder (measure the landable win)

`goFusedP` is the shape a *proven* version would have: no `bitpos` parameter
(it equals `pos*8 - cnt`, so the termination measure is
`((data.size - pos)*8 + cnt, data.size - pos)` over `pos`/`cnt` already threaded),
no out-of-range guard (provably dead under `pos ≤ data.size`), and the common
literal decoded inline (its `llen ≠ 0` check already guarantees ≥1 bit, so that
path needs no progress guard either). Only the non-literal `decodeSym` path keeps
a cheap `cnt`-based no-progress guard. `partial` here just to measure; the real
PR proves termination from the measure above. -/
def goFusedP (litTable distTable : HuffTree.DecodeTable)
    (data : ByteArray) (litTree distTree : HuffTree) (maxOut : Nat)
    (pos : Nat) (bitBuf : UInt64) (cnt : Nat) (output : ByteArray) :
    Except String (ByteArray × Nat × UInt64 × Nat) := do
  if hrc : cnt ≤ 56 ∧ pos < data.size then
    goFusedP litTable distTable data litTree distTree maxOut
      (pos + 1) (bitBuf ||| ((data[pos]'hrc.2).toUInt64 <<< cnt.toUInt64)) (cnt + 8) output
  else
  if hlit : (litTable.lenAt (bitBuf &&& 0x7FF).toNat).toNat ≠ 0
      ∧ (litTable.lenAt (bitBuf &&& 0x7FF).toNat).toNat ≤ cnt
      ∧ litTable.symAt (bitBuf &&& 0x7FF).toNat < 256 then
    if output.size ≥ maxOut then throw "Inflate: output exceeds maximum size"
    else
      goFusedP litTable distTable data litTree distTree maxOut pos
        (bitBuf >>> ((litTable.lenAt (bitBuf &&& 0x7FF).toNat).toNat).toUInt64)
        (cnt - (litTable.lenAt (bitBuf &&& 0x7FF).toNat).toNat)
        (output.push (litTable.symAt (bitBuf &&& 0x7FF).toNat).toUInt8)
  else
  let cnt0 := cnt
  match decodeSym litTree litTable bitBuf cnt with
  | .error e => .error e
  | .ok (sym, bitBuf, cnt, _used) =>
    if sym < 256 then
      if output.size ≥ maxOut then throw "Inflate: output exceeds maximum size"
      else if hnp : cnt0 ≤ cnt then throw "Inflate: no progress in Huffman decode"
      else goFusedP litTable distTable data litTree distTree maxOut pos bitBuf cnt (output.push sym.toUInt8)
    else if sym == 256 then .ok (output, pos, bitBuf, cnt)
    else
      let idx := sym.toNat - 257
      if h : idx ≥ Inflate.lengthBase.size then throw s!"Inflate: invalid length code {sym}"
      else
        let base := Inflate.lengthBase[idx]
        let extra := Inflate.lengthExtra[idx]'(by simp [Inflate.lengthExtra_size, Inflate.lengthBase_size] at h ⊢; omega)
        let (extraBits, bitBuf, cnt) ← takeBits bitBuf cnt extra.toNat
        let length := base.toNat + extraBits
        match decodeSym distTree distTable bitBuf cnt with
        | .error e => .error e
        | .ok (distSym, bitBuf, cnt, _dused) =>
          let dIdx := distSym.toNat
          if h : dIdx ≥ Inflate.distBase.size then throw s!"Inflate: invalid distance code {distSym}"
          else
            let dBase := Inflate.distBase[dIdx]
            let dExtra := Inflate.distExtra[dIdx]'(by simp [Inflate.distExtra_size, Inflate.distBase_size] at h ⊢; omega)
            let (dExtraBits, bitBuf, cnt) ← takeBits bitBuf cnt dExtra.toNat
            let distance := dBase.toNat + dExtraBits
            if h0 : distance = 0 then throw s!"Inflate: zero back-reference distance"
            else if hds : distance > output.size then
              throw s!"Inflate: distance {distance} exceeds output size {output.size}"
            else if output.size + length > maxOut then throw "Inflate: output exceeds maximum size"
            else if hnp : cnt0 ≤ cnt then throw "Inflate: no progress in Huffman decode"
            else
              let out := Inflate.copyLoop output (output.size - distance) distance 0 length (by omega) (by omega)
              goFusedP litTable distTable data litTree distTree maxOut pos bitBuf cnt out
  termination_by (data.size - pos) * 9 + cnt
  decreasing_by
    · -- refill: pos < data.size, so (size-pos)*9 drops by 9 while cnt rises 8 → net −1
      obtain ⟨_, hp⟩ := hrc; omega
    · -- inline literal: cnt drops by llen ≥ 1
      obtain ⟨hne, hle, _⟩ := hlit; omega
    · -- decodeSym literal: cnt < cnt0 from the no-progress guard
      omega
    · -- match: cnt < cnt0 from the no-progress guard
      omega
set_option maxRecDepth 4096 in
/-- USize-threaded twin of `goFusedP`: carries the byte cursor `pos` and the bit
    count `cnt` as raw `USize` words, so the per-symbol refill (`pos+1`, `cnt+8`)
    and the inline-literal consume (`cnt - len`) compile to machine adds/subs with
    no boxed-`Nat` arithmetic or `lean_dec` traffic; the refill byte read uses
    `ByteArray.uget` (an unchecked `size_t` index). Only the rarer back-reference /
    long-code path round-trips `cnt` through `Nat` to reuse `decodeSym`/`takeBits`
    unchanged. Proven equal to `goFusedP` (`goFusedPU_eq`) under buffer
    addressability `data.size < USize.size`, hence to the reference decoder.
    Termination measure mirrors `goFusedP`'s `(data.size - pos)*9 + cnt`, read
    through `toNat`; the branch guards (`cnt ≤ 56`, `len ≤ cnt`, the no-progress
    check) supply the no-overflow facts, so the only proof argument is `hsz`. -/
def goFusedPU (litTable distTable : HuffTree.DecodeTable)
    (data : ByteArray) (litTree distTree : HuffTree) (maxOut : Nat)
    (pos : USize) (bitBuf : UInt64) (cnt : USize)
    (hsz : data.size < USize.size) (output : ByteArray) :
    Except String (ByteArray × USize × UInt64 × USize) := do
  if hrc : cnt ≤ 56 ∧ pos < data.size.toUSize then
    goFusedPU litTable distTable data litTree distTree maxOut
      (pos + 1)
      (bitBuf ||| ((data.uget pos (by
          have h := USize.lt_iff_toNat_lt.mp hrc.2
          rwa [toUSize_toNat_of_lt hsz] at h)).toUInt64 <<< cnt.toUInt64))
      (cnt + 8) hsz output
  else
  if hlit : (litTable.lenAt (bitBuf &&& 0x7FF).toNat).toNat ≠ 0
      ∧ ((litTable.lenAt (bitBuf &&& 0x7FF).toNat).toNat).toUSize ≤ cnt
      ∧ litTable.symAt (bitBuf &&& 0x7FF).toNat < 256 then
    if output.size ≥ maxOut then throw "Inflate: output exceeds maximum size"
    else
      goFusedPU litTable distTable data litTree distTree maxOut pos
        (bitBuf >>> ((litTable.lenAt (bitBuf &&& 0x7FF).toNat).toNat).toUInt64)
        (cnt - ((litTable.lenAt (bitBuf &&& 0x7FF).toNat).toNat).toUSize)
        hsz
        (output.push (litTable.symAt (bitBuf &&& 0x7FF).toNat).toUInt8)
  else
  let cnt0 := cnt.toNat
  match decodeSym litTree litTable bitBuf cnt.toNat with
  | .error e => .error e
  | .ok (sym, bitBuf, cnt', _used) =>
    if sym < 256 then
      if output.size ≥ maxOut then throw "Inflate: output exceeds maximum size"
      else if hnp : cnt0 ≤ cnt' then throw "Inflate: no progress in Huffman decode"
      else
        goFusedPU litTable distTable data litTree distTree maxOut pos bitBuf
          cnt'.toUSize hsz (output.push sym.toUInt8)
    else if sym == 256 then .ok (output, pos, bitBuf, cnt'.toUSize)
    else
      let idx := sym.toNat - 257
      if h : idx ≥ Inflate.lengthBase.size then throw s!"Inflate: invalid length code {sym}"
      else
        let base := Inflate.lengthBase[idx]
        let extra := Inflate.lengthExtra[idx]'(by simp [Inflate.lengthExtra_size, Inflate.lengthBase_size] at h ⊢; omega)
        let (extraBits, bitBuf, cnt'') ← takeBits bitBuf cnt' extra.toNat
        let length := base.toNat + extraBits
        match decodeSym distTree distTable bitBuf cnt'' with
        | .error e => .error e
        | .ok (distSym, bitBuf, cnt3, _dused) =>
          let dIdx := distSym.toNat
          if h : dIdx ≥ Inflate.distBase.size then throw s!"Inflate: invalid distance code {distSym}"
          else
            let dBase := Inflate.distBase[dIdx]
            let dExtra := Inflate.distExtra[dIdx]'(by simp [Inflate.distExtra_size, Inflate.distBase_size] at h ⊢; omega)
            let (dExtraBits, bitBuf, cnt4) ← takeBits bitBuf cnt3 dExtra.toNat
            let distance := dBase.toNat + dExtraBits
            if h0 : distance = 0 then throw s!"Inflate: zero back-reference distance"
            else if hds : distance > output.size then
              throw s!"Inflate: distance {distance} exceeds output size {output.size}"
            else if output.size + length > maxOut then throw "Inflate: output exceeds maximum size"
            else if hnp : cnt0 ≤ cnt4 then throw "Inflate: no progress in Huffman decode"
            else
              let out := Inflate.copyLoop output (output.size - distance) distance 0 length (by omega) (by omega)
              goFusedPU litTable distTable data litTree distTree maxOut pos bitBuf
                cnt4.toUSize hsz out
  termination_by (data.size - pos.toNat) * 9 + cnt.toNat
  decreasing_by
    · -- refill: pos < data.size, so (size - pos)*9 drops by 9 while cnt rises 8 → net −1
      obtain ⟨hc, hp⟩ := hrc
      have hbig : (64 : Nat) < 2 ^ System.Platform.numBits :=
        USize.size_eq_two_pow ▸ Nat.lt_of_lt_of_le (by decide) USize.le_size
      have hpn : pos.toNat < data.size := by
        have h := USize.lt_iff_toNat_lt.mp hp; rwa [toUSize_toNat_of_lt hsz] at h
      have hcn : cnt.toNat ≤ 56 := by
        have h := USize.le_iff_toNat_le.mp hc
        rwa [USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)] at h
      have hpa : (pos + 1).toNat = pos.toNat + 1 := by
        rw [USize.toNat_add, USize.toNat_one]; apply Nat.mod_eq_of_lt
        have : pos.toNat + 1 < USize.size := by omega
        exact USize.size_eq_two_pow ▸ this
      have h8 : (8 : USize).toNat = 8 :=
        USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)
      have hca : (cnt + 8).toNat = cnt.toNat + 8 := by
        rw [USize.toNat_add, h8]; apply Nat.mod_eq_of_lt; omega
      rw [hpa, hca]; omega
    · -- inline literal: cnt drops by len ≥ 1
      obtain ⟨hne, hle, _⟩ := hlit
      have hlen : ((litTable.lenAt (bitBuf &&& 0x7FF).toNat).toNat).toUSize.toNat
          = (litTable.lenAt (bitBuf &&& 0x7FF).toNat).toNat :=
        toUSize_toNat_of_lt (UInt8.toNat_lt_usizeSize _)
      have hsub : (cnt - ((litTable.lenAt (bitBuf &&& 0x7FF).toNat).toNat).toUSize).toNat
          = cnt.toNat - (litTable.lenAt (bitBuf &&& 0x7FF).toNat).toNat := by
        rw [USize.toNat_sub_of_le _ _ hle, hlen]
      have hlecnt : (litTable.lenAt (bitBuf &&& 0x7FF).toNat).toNat ≤ cnt.toNat :=
        hlen ▸ USize.le_iff_toNat_le.mp hle
      rw [hsub]; omega
    · -- slow literal: cnt' < cnt0 = cnt.toNat from the no-progress guard
      have hcsz : cnt.toNat < USize.size := cnt.toNat_lt_two_pow_numBits
      have hb : cnt'.toUSize.toNat = cnt' := toUSize_toNat_of_lt (by omega)
      rw [hb]; omega
    · -- back-reference: cnt4 < cnt0 = cnt.toNat from the no-progress guard
      have hcsz : cnt.toNat < USize.size := cnt.toNat_lt_two_pow_numBits
      have hb : cnt4.toUSize.toNat = cnt4 := toUSize_toNat_of_lt (by omega)
      rw [hb]; omega

/-- The production symbol loop: when the input is `USize`-addressable (always true
    at runtime — the check is one `USize` round-trip, no bignum compare), run the
    unboxed `goFusedPU`, converting `pos`/`cnt` to `USize` at entry and back to `Nat`
    at exit; otherwise fall back to the boxed-`Nat` `goFusedP`. The two agree
    (`Zip.Spec.InflateBufCorrect.goFusedPDispatch_eq`), so the result is identical to
    `goFusedP` and hence to the reference decoder.

    Internal helper: the equivalence holds under the loop's entry invariants
    `pos ≤ data.size` and `cnt ≤ 64` (a refilled buffer holds at most 64 bits),
    which `decodeHuffmanFastBuf` always satisfies (they come from the `BufCorr`
    carried into the loop). With `pos`/`cnt` outside those bounds the addressable
    branch could `toUSize`-wrap, so this is not a general-purpose entry point. -/
@[inline] def goFusedPDispatch (litTable distTable : HuffTree.DecodeTable)
    (data : ByteArray) (litTree distTree : HuffTree) (maxOut : Nat)
    (pos : Nat) (bitBuf : UInt64) (cnt : Nat) (output : ByteArray) :
    Except String (ByteArray × Nat × UInt64 × Nat) :=
  if hsz : data.size.toUSize.toNat = data.size then
    Except.map (fun x => (x.1, x.2.1.toNat, x.2.2.1, x.2.2.2.toNat))
      (goFusedPU litTable distTable data litTree distTree maxOut
        pos.toUSize bitBuf cnt.toUSize
        (by rw [← hsz]; exact USize.toNat_lt_two_pow_numBits _) output)
  else
    goFusedP litTable distTable data litTree distTree maxOut pos bitBuf cnt output

/-- Wide-buffer replacement for `Inflate.decodeHuffmanFastBR`: convert the
    `BitReader` to a scalar buffer, run the loop, convert back. -/
def decodeHuffmanFastBuf (br : BitReader) (output : ByteArray)
    (litTree distTree : HuffTree) (maxOut : Nat) :
    Except String (ByteArray × BitReader) := do
  let litTable := litTree.buildTable
  let distTable := distTree.buildTable
  let (pos, bitBuf, cnt) := refill br.data br.pos 0 0
  -- align: drop the bitOff bits already consumed in the first byte
  let bitBuf := bitBuf >>> br.bitOff.toUInt64
  let cnt := cnt - br.bitOff
  -- `goFusedPDispatch` runs the unboxed `goFusedPU` (USize `pos`/`cnt`) when the
  -- input is addressable, else the boxed `goFusedP`. Both are the guard-light loop
  -- (no threaded `bitpos`, no provably-dead out-of-range guard, common literal
  -- inline), proven equal to `goFused` (`goFusedP_eq` / `goFusedPDispatch_eq`).
  let (out, pos', bitBuf', cnt') ←
    goFusedPDispatch litTable distTable br.data litTree distTree maxOut pos bitBuf cnt output
  let _ := bitBuf'
  let endbit := pos' * 8 - cnt'
  .ok (out, { data := br.data, pos := endbit / 8, bitOff := endbit % 8 })

end InflateBuf

namespace Inflate

/-- The fast Huffman block decoder used by `inflateLoop`: delegates to the
    wide-buffer implementation `InflateBuf.decodeHuffmanFastBuf`, which is proven
    equal to the BitReader reference `decodeHuffmanFastBR` and hence to the
    canonical `decodeHuffman` (`Zip.Spec.InflateBufCorrect.decodeHuffmanFast_eq`).
    Same signature as `decodeHuffmanFastBR`, so `inflateLoop`'s body and every
    downstream correctness proof transfer with a single (now conditional) rewrite. -/
protected def decodeHuffmanFast (br : BitReader) (output : ByteArray)
    (litTree distTree : HuffTree) (maxOutputSize : Nat)
    : Except String (ByteArray × BitReader) :=
  InflateBuf.decodeHuffmanFastBuf br output litTree distTree maxOutputSize

/-- Block loop for DEFLATE decompression. Decodes blocks until a final block
    is seen. Uses well-founded recursion on the remaining bits in the stream. -/
def inflateLoop (br : BitReader) (output : ByteArray)
    (fixedLit fixedDist : HuffTree) (maxOutputSize : Nat)
    (dataSize : Nat) : Except String (ByteArray × Nat) := do
    let (bfinal, br₁) ← br.readBits 1
    let (btype, br₂) ← br₁.readBits 2
    let (output', br') ← match btype with
      | 0 => Inflate.decodeStored br₂ output maxOutputSize
      | 1 => Inflate.decodeHuffmanFast br₂ output fixedLit fixedDist maxOutputSize
      | 2 => do
        let (litTree, distTree, br₃) ← decodeDynamicTrees br₂
        Inflate.decodeHuffmanFast br₃ output litTree distTree maxOutputSize
      | _ => throw s!"Inflate: reserved block type {btype}"
    if bfinal == 1 then
      let aligned := br'.alignToByte
      return (output', aligned.pos)
    else
      -- Guard: bit position must advance for WF termination
      if _h₁ : br'.bitPos ≤ br.bitPos then
        throw "Inflate: no progress in inflate loop"
      else if _h₂ : dataSize * 8 < br'.bitPos then
        throw "Inflate: bit position out of range"
      else
        inflateLoop br' output' fixedLit fixedDist maxOutputSize dataSize
termination_by dataSize * 8 - br.bitPos
decreasing_by all_goals omega

/-- Inflate a raw DEFLATE stream starting at byte offset `startPos`. Returns the
    decompressed data and the byte-aligned position after the last DEFLATE block.
    `maxOutputSize` (default 1 GiB) limits decompressed output to guard against
    zip bombs.

    `sizeHint` pre-reserves capacity for the output buffer (`0`, the default,
    reserves nothing — `ByteArray.emptyWithCapacity 0 = .empty`). When the caller
    knows the decompressed size (gzip ISIZE, the ZIP local/central header), passing
    it removes the doubling reallocations (`lean_copy_sarray`) that a buffer grown
    one literal at a time otherwise pays. The hint is a capacity hint only: it never
    affects the produced bytes or the `maxOutputSize` bomb guard, so every inflate
    correctness proof transfers unchanged (`ByteArray.emptyWithCapacity n` is
    definitionally `{ data := Array.empty }` for every `n`). -/
def inflateRawReference (data : ByteArray) (startPos : Nat := 0)
    (maxOutputSize : Nat := 1024 * 1024 * 1024) (sizeHint : Nat := 0) :
    Except String (ByteArray × Nat) := do
  let br : BitReader := { data, pos := startPos, bitOff := 0 }
  let fixedLit ← HuffTree.fromLengths fixedLitLengths
  let fixedDist ← HuffTree.fromLengths fixedDistLengths
  inflateLoop br (ByteArray.emptyWithCapacity sizeHint) fixedLit fixedDist maxOutputSize data.size

/-- Inflate a raw DEFLATE stream. Processes blocks until a final block is seen.
    `maxOutputSize` (default 1 GiB) caps decompressed output as a zip-bomb
    guard. Unlike the FFI path, where `maxDecompressedSize := 0` means
    unlimited, here `0` rejects any non-empty output (the comparison is
    `output.size + len > maxOutputSize`, so even a single produced byte
    exceeds the bound). Overflow raises an `Except` error containing
    `"Inflate: output exceeds maximum size"`.
    See `SECURITY_INVENTORY.md` *Decompression Limit Inventory*.

    `sizeHint` pre-reserves output capacity when the decompressed size is known;
    `0` (the default) reserves nothing. See `inflateRaw`. -/
def inflateReference (data : ByteArray) (maxOutputSize : Nat := 1024 * 1024 * 1024)
    (sizeHint : Nat := 0) :
    Except String ByteArray := do
  let (output, _) ← inflateRawReference data 0 maxOutputSize sizeHint
  return output

/-- The output capacity hint is computationally inert: `inflateRawReference` with any
    `sizeHint` equals it with the default `sizeHint := 0`, because
    `ByteArray.emptyWithCapacity n` reduces to `{ data := Array.empty }` for every
    `n` (capacity is a runtime-only allocation hint). -/
@[simp] theorem inflateRawReference_sizeHint_eq (data : ByteArray)
    (startPos maxOutputSize sizeHint : Nat) :
    inflateRawReference data startPos maxOutputSize sizeHint
      = inflateRawReference data startPos maxOutputSize :=
  rfl

/-- `inflateReference` with any `sizeHint` equals it with the default `0`. -/
@[simp] theorem inflateReference_sizeHint_eq (data : ByteArray) (maxOutputSize sizeHint : Nat) :
    inflateReference data maxOutputSize sizeHint = inflateReference data maxOutputSize :=
  rfl

end Inflate
end Zip.Native
