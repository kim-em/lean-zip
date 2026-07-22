import ZipCommon.Binary
import Std.Tactic.BVDecide

/-! # Packed token container for the LZ77 stream

The DEFLATE encoder emits a stream of `LZ77Token`s.  In production these are
bit-packed one-per-`UInt32` by `packTok`/`unpackTok` (see `Zip/Native/Deflate.lean`)
and accumulated in an `Array UInt32`.  Lean stores `Array UInt32` with 8-byte
boxed slots, so 45.9M tokens cost ~367 MB — the dominant page-fault / system-time
cost on a whole-tar compress.

This file introduces `TokenArray`, a newtype over a `ByteArray` that stores each
token in exactly 4 little-endian bytes (halving the footprint to 4 B/token).  It
is a *pure addition*: nothing consumes it yet.  Later stages retype the LZ77
producers and consumers to `TokenArray`, one `*Correct.lean` file at a time.

The proof-facing model stays `Array UInt32`: `TokenArray.toArray` exposes the
`Array UInt32` view, and the four bridge lemmas

* `empty_toArray`   `TokenArray.empty.toArray = #[]`
* `push_toArray`    `(ta.push w).toArray = ta.toArray.push w`
* `size_toArray`    `ta.size = ta.toArray.size`
* `get_toArray`     `ta.get i h = ta.toArray[i]`

let the existing packed-layer proofs port by substituting the array-map lemmas
(e.g. `Array.map_push`) with `push_toArray`, while the additive-delta lemmas in
`DeflateFreqsAdditive` keep reasoning on `Array UInt32`.

The `TokenArray` invariant `bytes.size % 4 = 0` is carried as a proof field
(erased at runtime, so the footprint is exactly the `ByteArray`).  The invariant
is precisely 4-byte *alignment* of the underlying `ByteArray` — the constructor
accepts any byte length that is a multiple of four, not only streams built via
`empty`/`push`.  In practice every `TokenArray` value is produced by `empty`,
`push`, and `extract`, each of which discharges the alignment obligation, and it
is that alignment invariant (not the construction provenance) that makes the
bridge lemmas unconditional. -/

namespace ByteArray

/-- Append a `UInt32` as four little-endian bytes (low byte first), matching
    `Binary.writeUInt32LE` / `Binary.readUInt32LE`.  Four `push`es keep the growth
    in place (amortised O(1)) rather than allocating a temporary.

    TODO upstream to lean-zip-common (alongside `Binary.writeUInt32LE`). -/
@[inline] def pushUInt32LE (b : ByteArray) (v : UInt32) : ByteArray :=
  (((b.push v.toUInt8).push (v >>> 8).toUInt8).push (v >>> 16).toUInt8).push (v >>> 24).toUInt8

@[simp] theorem size_pushUInt32LE (b : ByteArray) (v : UInt32) :
    (b.pushUInt32LE v).size = b.size + 4 := by
  simp [pushUInt32LE, ByteArray.size_push]

/-- Underlying byte list of `pushUInt32LE`: the original bytes followed by the
    four little-endian bytes of `v`. -/
theorem pushUInt32LE_data_toList (b : ByteArray) (v : UInt32) :
    (b.pushUInt32LE v).data.toList =
      b.data.toList ++
        [v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8] := by
  simp [pushUInt32LE, ByteArray.data_push, Array.toList_push]

private theorem length_data_toList (b : ByteArray) : b.data.toList.length = b.size := by
  rw [Array.length_toList]; rfl

/-- `pushUInt32LE` preserves the earlier bytes. -/
theorem getElem_pushUInt32LE_lt (b : ByteArray) (v : UInt32) {j : Nat}
    (hj : j < b.size) (h : j < (b.pushUInt32LE v).size) :
    (b.pushUInt32LE v)[j]'h = b[j]'hj := by
  rw [ByteArray.getElem_eq_getElem_data, ByteArray.getElem_eq_getElem_data,
      ← Array.getElem_toList, ← Array.getElem_toList]
  apply Option.some.inj
  rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, pushUInt32LE_data_toList,
      List.getElem?_append_left (by rw [length_data_toList]; exact hj)]

/-- The `k`-th appended byte (`k < 4`) of `pushUInt32LE` sits at offset `b.size + k`. -/
theorem getElem_pushUInt32LE_offset (b : ByteArray) (v : UInt32) {k : Nat}
    (hk : k < 4) (h : b.size + k < (b.pushUInt32LE v).size) :
    (b.pushUInt32LE v)[b.size + k]'h =
      [v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8][k]'(by simpa using hk) := by
  rw [ByteArray.getElem_eq_getElem_data, ← Array.getElem_toList]
  apply Option.some.inj
  rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, pushUInt32LE_data_toList,
      List.getElem?_append_right (by rw [length_data_toList]; omega)]
  simp

/-- The first appended byte of `pushUInt32LE` sits at offset `b.size` (the
    `k = 0` case of `getElem_pushUInt32LE_offset`, stated without the `+ 0`). -/
theorem getElem_pushUInt32LE_size (b : ByteArray) (v : UInt32)
    (h : b.size < (b.pushUInt32LE v).size) :
    (b.pushUInt32LE v)[b.size]'h = v.toUInt8 := by
  have := getElem_pushUInt32LE_offset b v (k := 0) (by omega) h
  simpa using this

/-- Reassembling the four little-endian bytes of a `UInt32` recovers it. -/
theorem uint32_le_roundtrip (v : UInt32) :
    v.toUInt8.toUInt32 ||| ((v >>> 8).toUInt8.toUInt32 <<< 8)
      ||| ((v >>> 16).toUInt8.toUInt32 <<< 16) ||| ((v >>> 24).toUInt8.toUInt32 <<< 24) = v := by
  bv_decide

end ByteArray

/-- A packed LZ77 token stream: one token per four little-endian bytes.
    The `aligned` field records that the byte length is a multiple of four; it is
    a `Prop` (erased at runtime), so the runtime footprint is just `bytes`. -/
structure TokenArray where
  bytes : ByteArray
  aligned : bytes.size % 4 = 0

namespace TokenArray

/-- The empty token stream. -/
def empty : TokenArray := ⟨ByteArray.empty, by simp [ByteArray.size_empty]⟩

/-- Number of tokens (four bytes each). -/
def size (ta : TokenArray) : Nat := ta.bytes.size / 4

/-- Append one packed token (its little-endian `UInt32` word). -/
def push (ta : TokenArray) (w : UInt32) : TokenArray :=
  ⟨ta.bytes.pushUInt32LE w, by
    have := ta.aligned
    rw [ByteArray.size_pushUInt32LE]; omega⟩

theorem size_push (ta : TokenArray) (w : UInt32) : (ta.push w).size = ta.size + 1 := by
  have := ta.aligned
  simp only [push, size, ByteArray.size_pushUInt32LE]
  omega

private theorem byte_bound (ta : TokenArray) {i : Nat} (h : i < ta.size) :
    4 * i + 3 < ta.bytes.size := by
  have := ta.aligned
  simp only [size] at h
  omega

/-- Read the `i`-th token as a little-endian `UInt32` (proven-in-bounds). -/
def get (ta : TokenArray) (i : Nat) (h : i < ta.size) : UInt32 :=
  have hb := ta.byte_bound h
  (ta.bytes[4 * i]'(by omega)).toUInt32
    ||| ((ta.bytes[4 * i + 1]'(by omega)).toUInt32 <<< 8)
    ||| ((ta.bytes[4 * i + 2]'(by omega)).toUInt32 <<< 16)
    ||| ((ta.bytes[4 * i + 3]'(by omega)).toUInt32 <<< 24)

/-- The `Array UInt32` model: the token at each index. -/
def toArray (ta : TokenArray) : Array UInt32 :=
  Array.ofFn (n := ta.size) (fun i => ta.get i.val i.isLt)

/-! ## Bridge lemmas relating `TokenArray` to its `Array UInt32` model. -/

@[simp] theorem empty_toArray : empty.toArray = #[] := by
  apply Array.eq_empty_of_size_eq_zero
  simp only [toArray, Array.size_ofFn, size, empty, ByteArray.size_empty]

theorem size_toArray (ta : TokenArray) : ta.size = ta.toArray.size := by
  simp only [toArray, Array.size_ofFn]

theorem get_toArray (ta : TokenArray) (i : Nat) (h : i < ta.size) :
    ta.get i h = ta.toArray[i]'(by rw [← size_toArray]; exact h) := by
  simp only [toArray, Array.getElem_ofFn]

/-- `get` ignores a subsequent `push` on earlier tokens. -/
private theorem get_push_lt (ta : TokenArray) (w : UInt32) {i : Nat} (h : i < ta.size)
    (h' : i < (ta.push w).size) :
    (ta.push w).get i h' = ta.get i h := by
  have hb := ta.byte_bound h
  simp only [get, push]
  rw [ByteArray.getElem_pushUInt32LE_lt ta.bytes w (by omega),
      ByteArray.getElem_pushUInt32LE_lt ta.bytes w (by omega),
      ByteArray.getElem_pushUInt32LE_lt ta.bytes w (by omega),
      ByteArray.getElem_pushUInt32LE_lt ta.bytes w (by omega)]

/-- `get` at the fresh index reads back the just-pushed token. -/
private theorem get_push_eq (ta : TokenArray) (w : UInt32)
    (h' : ta.size < (ta.push w).size) :
    (ta.push w).get ta.size h' = w := by
  have haligned := ta.aligned
  have hsz : 4 * ta.size = ta.bytes.size := by simp only [size]; omega
  simp only [get, push, hsz]
  rw [ByteArray.getElem_pushUInt32LE_size ta.bytes w (by simp),
      ByteArray.getElem_pushUInt32LE_offset ta.bytes w (k := 1) (by omega) (by simp),
      ByteArray.getElem_pushUInt32LE_offset ta.bytes w (k := 2) (by omega) (by simp),
      ByteArray.getElem_pushUInt32LE_offset ta.bytes w (k := 3) (by omega) (by simp)]
  simpa using ByteArray.uint32_le_roundtrip w

/-- Byte-level slice on token boundaries: tokens `[i, j)` as a fresh
    `TokenArray`.  Because every token is exactly four bytes, the token range
    `[i, j)` is the byte range `[4·i, 4·j)`, and the alignment invariant is
    preserved (a difference of multiples of four).  This is the packed twin of
    `Array.extract` — the shared-block split family slices the token stream with
    it, and `extract_toArray` bridges it to the `Array UInt32` model. -/
def extract (ta : TokenArray) (i j : Nat) : TokenArray :=
  ⟨ta.bytes.extract (4 * i) (4 * j), by
    have := ta.aligned
    rw [ByteArray.size_extract]; omega⟩

@[simp] theorem size_extract (ta : TokenArray) (i j : Nat) :
    (ta.extract i j).size = min j ta.size - i := by
  have := ta.aligned
  simp only [extract, size, ByteArray.size_extract]
  omega

/-- Reading token `k` of `ta.extract i j` reads token `i + k` of `ta`. -/
theorem get_extract (ta : TokenArray) (i j k : Nat) (h : k < (ta.extract i j).size)
    (h' : i + k < ta.size) :
    (ta.extract i j).get k h = ta.get (i + k) h' := by
  simp only [get, extract]
  have key : ∀ (a b : Nat) (hla : a < (ta.bytes.extract (4 * i) (4 * j)).size)
      (hlb : b < ta.bytes.size), 4 * i + a = b →
      (ta.bytes.extract (4 * i) (4 * j))[a]'hla = ta.bytes[b]'hlb := by
    intro a b hla hlb hab
    rw [ByteArray.getElem_extract]; congr 1
  rw [key (4 * k) (4 * (i + k)) _ _ (by omega),
      key (4 * k + 1) (4 * (i + k) + 1) _ _ (by omega),
      key (4 * k + 2) (4 * (i + k) + 2) _ _ (by omega),
      key (4 * k + 3) (4 * (i + k) + 3) _ _ (by omega)]

/-- The load-bearing slice bridge: extracting a token range from the container
    matches extracting it from the `Array UInt32` model. -/
@[simp] theorem extract_toArray (ta : TokenArray) (i j : Nat) :
    (ta.extract i j).toArray = ta.toArray.extract i j := by
  apply Array.ext
  · rw [← size_toArray, size_extract, Array.size_extract, ← size_toArray]
  · intro k h1 h2
    have hk : k < (ta.extract i j).size := by rw [← size_toArray] at h1; exact h1
    have hik : i + k < ta.size := by
      rw [size_extract] at hk; omega
    rw [← get_toArray (ta.extract i j) k hk, get_extract ta i j k hk hik,
        Array.getElem_extract, get_toArray]

/-- The load-bearing bridge lemma: pushing a token onto the container matches
    pushing its word onto the `Array UInt32` model.  This is the drop-in
    replacement for `Array.map_push` in the ported packed-layer proofs. -/
@[simp] theorem push_toArray (ta : TokenArray) (w : UInt32) :
    (ta.push w).toArray = ta.toArray.push w := by
  apply Array.ext
  · rw [← size_toArray, size_push, size_toArray, Array.size_push]
  · intro i h1 h2
    have hlt : i < (ta.push w).size := by rw [← size_toArray] at h1; exact h1
    have hisize : i < ta.size + 1 := by rw [← size_push]; exact hlt
    rw [← get_toArray (ta.push w) i hlt]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hisize with hi | hi
    · rw [get_push_lt ta w hi hlt, get_toArray ta i hi,
          Array.getElem_push_lt (show i < ta.toArray.size by rw [← size_toArray]; exact hi)]
    · subst hi
      rw [get_push_eq, Array.getElem_push, dif_neg (by rw [← size_toArray]; omega)]

end TokenArray
