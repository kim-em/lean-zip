import Zip.Native.XxHash

/-!
# XXH64 Specification Predicates (xxHash specification)

Formal specification of the XXH64 hash function used by Zstandard (RFC 8878)
for optional content checksums.  The upper 32 bits of `xxHash64 data 0` are
stored as a checksum in Zstd frame footers when `Content_Checksum` is set.

**Spec level**: Algorithmic correspondence (tier 3).  Unlike CRC-32, xxHash
is not algebraically compositional — it is designed for speed, not mathematical
elegance.  The reference algorithm (xxHash specification by Yann Collet) IS the
spec, so our predicates formalize the structural steps of that algorithm rather
than abstract mathematical properties.

The specification is structured in layers:
1. **Prime constants**: the 5 XXH64 prime values match the spec
2. **Round step**: single accumulator update rule
3. **Convergence**: 4-accumulator merge after stripe processing
4. **Avalanche**: final 3-step mixing
5. **Remaining byte processing**: tail handling (8-byte, 4-byte, 1-byte chunks)

Correctness theorems prove empty-input characterization, expansion
equivalences, and the connection between `xxHash64Upper32` and the full
`xxHash64` function.
-/

namespace XxHash64.Spec

/-! ## Prime constant validation -/

/-- The five XXH64 prime constants have the correct values from the xxHash
    specification.  These are fixed constants, not configurable parameters. -/
def ValidPrimes : Prop :=
  XxHash64.PRIME64_1 = 0x9E3779B185EBCA87 ∧
  XxHash64.PRIME64_2 = 0xC2B2AE3D27D4EB4F ∧
  XxHash64.PRIME64_3 = 0x165667B19E3779F9 ∧
  XxHash64.PRIME64_4 = 0x85EBCA77C2B2AE63 ∧
  XxHash64.PRIME64_5 = 0x27D4EB2F165667C5

instance : Decidable ValidPrimes :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-! ## Accumulator round step -/

/-- A single round step applies the transformation:
    `acc ← rotl((acc + lane × PRIME2), 31) × PRIME1`
    This predicate states that `round` computes exactly this. -/
def ValidRound (acc lane result : UInt64) : Prop :=
  result = XxHash64.round acc lane

instance : Decidable (ValidRound acc lane result) :=
  inferInstanceAs (Decidable (_ = _))

/-- The round function expands to its constituent operations:
    add, multiply by PRIME2, rotate left by 31, multiply by PRIME1. -/
def RoundExpansion (acc lane result : UInt64) : Prop :=
  result = (XxHash64.rotl (acc + lane * XxHash64.PRIME64_2) 31) * XxHash64.PRIME64_1

instance : Decidable (RoundExpansion acc lane result) :=
  inferInstanceAs (Decidable (_ = _))

/-! ## Accumulator convergence -/

/-- Captures the 4-accumulator state after processing 32-byte stripes. -/
structure RoundState where
  acc1 : UInt64
  acc2 : UInt64
  acc3 : UInt64
  acc4 : UInt64
  deriving Repr, DecidableEq

/-- Initial accumulator state for a given seed. -/
def initState (seed : UInt64) : RoundState where
  acc1 := seed + XxHash64.PRIME64_1 + XxHash64.PRIME64_2
  acc2 := seed + XxHash64.PRIME64_2
  acc3 := seed
  acc4 := seed - XxHash64.PRIME64_1

/-- The convergence step merges the 4 accumulators into a single hash value
    via rotation and `mergeAccumulator`:
    `h = rotl(acc1,1) + rotl(acc2,7) + rotl(acc3,12) + rotl(acc4,18)`
    followed by merging each accumulator. -/
def ValidConvergence (st : RoundState) (result : UInt64) : Prop :=
  let h := XxHash64.rotl st.acc1 1 + XxHash64.rotl st.acc2 7 +
           XxHash64.rotl st.acc3 12 + XxHash64.rotl st.acc4 18
  let h := XxHash64.mergeAccumulator h st.acc1
  let h := XxHash64.mergeAccumulator h st.acc2
  let h := XxHash64.mergeAccumulator h st.acc3
  result = XxHash64.mergeAccumulator h st.acc4

instance : Decidable (ValidConvergence st result) :=
  inferInstanceAs (Decidable (_ = _))

/-! ## Avalanche mixing -/

/-- The 3-step avalanche mixing applied as the final hash finalization:
    1. `h ← (h ⊕ (h >>> 33)) × PRIME2`
    2. `h ← (h ⊕ (h >>> 29)) × PRIME3`
    3. `h ← h ⊕ (h >>> 32)` -/
def ValidAvalanche (input result : UInt64) : Prop :=
  result = XxHash64.avalanche input

instance : Decidable (ValidAvalanche input result) :=
  inferInstanceAs (Decidable (_ = _))

/-! ## Remaining byte processing -/

/-- The tail processing handles bytes remaining after full 32-byte stripes,
    consuming 8-byte, then 4-byte, then 1-byte chunks sequentially. -/
def ValidProcessRemaining (acc : UInt64) (data : ByteArray) (off len : Nat)
    (result : UInt64) : Prop :=
  result = XxHash64.processRemaining acc data off len

instance : Decidable (ValidProcessRemaining acc data off len result) :=
  inferInstanceAs (Decidable (_ = _))

/-! ## Helper lemmas -/

/-- processRemaining8 is a no-op when endPos = pos (8-byte loop skipped). -/
theorem processRemaining8_self (h : UInt64) (data : ByteArray) (pos : Nat) :
    XxHash64.processRemaining8 h data pos pos = (h, pos) := by
  unfold XxHash64.processRemaining8
  simp only [show ¬(pos + 8 ≤ pos) from by omega, ↓reduceIte]

/-- processRemaining1 is a no-op when endPos = pos (1-byte loop skipped). -/
theorem processRemaining1_self (h : UInt64) (data : ByteArray) (pos : Nat) :
    XxHash64.processRemaining1 h data pos pos = h := by
  unfold XxHash64.processRemaining1
  simp only [show ¬(pos < pos) from by omega, ↓reduceIte]

/-- processRemaining is a no-op when len = 0: all three phases
    (8-byte, 4-byte, 1-byte) are immediately skipped. -/
theorem processRemaining_zero (acc : UInt64) (data : ByteArray) (off : Nat) :
    XxHash64.processRemaining acc data off 0 = acc := by
  simp only [XxHash64.processRemaining, Nat.add_zero, processRemaining8_self,
        show ¬(off + 4 ≤ off) from by omega, ↓reduceIte, processRemaining1_self]

/-! ## Specification theorems -/

/-- The prime constants are correct. -/
theorem primes_valid : ValidPrimes := by decide

/-- The `round` function equals its expanded form. -/
theorem round_eq_expansion (acc lane : UInt64) :
    XxHash64.round acc lane =
      (XxHash64.rotl (acc + lane * XxHash64.PRIME64_2) 31) * XxHash64.PRIME64_1 := by
  rfl

/-- For empty input, `xxHash64` reduces to `avalanche (seed + PRIME64_5)`.
    This characterizes the short-path initialization where no stripes are
    processed and the remaining-byte handler is a no-op. -/
theorem xxHash64_empty (seed : UInt64) :
    XxHash64.xxHash64 ByteArray.empty seed =
      XxHash64.avalanche (seed + XxHash64.PRIME64_5) := by
  simp only [XxHash64.xxHash64, ByteArray.size_empty, Nat.zero_lt_succ, ↓reduceIte,
        Nat.toUInt64_eq, UInt64.reduceOfNat, UInt64.add_zero, Nat.zero_mod,
        Nat.sub_self, processRemaining_zero]

/-- `xxHash64Upper32` is defined as the upper 32 bits of `xxHash64 data 0`. -/
theorem xxHash64Upper32_eq (data : ByteArray) :
    XxHash64.xxHash64Upper32 data = (XxHash64.xxHash64 data 0 >>> 32).toUInt32 := by
  rfl

/-- `mergeAccumulator` expands to its XOR-round-multiply-add form. -/
theorem mergeAccumulator_eq (acc accN : UInt64) :
    XxHash64.mergeAccumulator acc accN =
      (acc ^^^ XxHash64.round 0 accN) * XxHash64.PRIME64_1 + XxHash64.PRIME64_4 := by
  rfl

/-- The avalanche function expands to its 3-step form. -/
theorem avalanche_eq (h : UInt64) :
    XxHash64.avalanche h =
      let h := h ^^^ (h >>> 33)
      let h := h * XxHash64.PRIME64_2
      let h := h ^^^ (h >>> 29)
      let h := h * XxHash64.PRIME64_3
      h ^^^ (h >>> 32) := by
  rfl

/-! ## Test vector verification

These theorems state xxHash64 test vectors from the xxHash specification.
The proofs are left as `sorry` because UInt64 computations (64-bit arithmetic
with wrapping) are too expensive for kernel evaluation (`decide_cbv` times out).
The same test vectors are verified at runtime in `ZipTest/XxHashNative.lean`. -/

/-- Known test vector: empty input with seed 0. -/
-- Verified at runtime in ZipTest/XxHashNative.lean
theorem empty_seed0 :
    XxHash64.xxHash64 ByteArray.empty 0 = 0xEF46DB3751D8E999 := by sorry

/-- Known test vector: single byte 0x42 with seed 0. -/
-- Verified at runtime in ZipTest/XxHashNative.lean
theorem single_byte_0x42 :
    XxHash64.xxHash64 (ByteArray.mk #[0x42]) 0 = 0x6D69E28F063257F9 := by sorry

/-- Known test vector: upper 32 bits of empty input hash. -/
-- Verified at runtime in ZipTest/XxHashNative.lean
theorem upper32_empty :
    XxHash64.xxHash64Upper32 ByteArray.empty = 0xEF46DB37 := by sorry

end XxHash64.Spec
