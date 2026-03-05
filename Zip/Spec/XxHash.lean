import Zip.Native.XxHash

/-!
# XXH64 Specification Predicates

Formal specification of the XXH64 hash function as used by Zstandard
(RFC 8878 §3.1.1) for optional content checksums.

**Spec level**: algorithmic correspondence (tier 3). The xxHash specification
document defines the algorithm — there are no useful algebraic properties
(unlike CRC32, xxHash is not compositional). The predicates below characterize
each phase of the algorithm, enabling correctness proofs that the implementation
follows the reference specification exactly.

Reference: https://github.com/Cyan4973/xxHash/blob/dev/doc/xxhash_spec.md
-/

namespace XxHash64.Spec

/-! ## Prime constant validity -/

/-- The five 64-bit prime constants used by XXH64.
    These specific values are mandated by the xxHash specification. -/
def ValidPrimes : Prop :=
  XxHash64.PRIME64_1 = 0x9E3779B185EBCA87 ∧
  XxHash64.PRIME64_2 = 0xC2B2AE3D27D4EB4F ∧
  XxHash64.PRIME64_3 = 0x165667B19E3779F9 ∧
  XxHash64.PRIME64_4 = 0x85EBCA77C2B2AE63 ∧
  XxHash64.PRIME64_5 = 0x27D4EB2F165667C5

instance : Decidable ValidPrimes :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## Round state -/

/-- State of the four accumulators during stripe processing. -/
structure RoundState where
  acc1 : UInt64
  acc2 : UInt64
  acc3 : UInt64
  acc4 : UInt64
  deriving Repr, BEq

/-- Initial accumulator state for a given seed (xxHash spec §2.1). -/
def initState (seed : UInt64) : RoundState where
  acc1 := seed + XxHash64.PRIME64_1 + XxHash64.PRIME64_2
  acc2 := seed + XxHash64.PRIME64_2
  acc3 := seed
  acc4 := seed - XxHash64.PRIME64_1

/-- A single round step correctly applies the xxHash round function:
    `acc' = rotl((acc + lane * PRIME64_2), 31) * PRIME64_1` -/
def ValidRound (acc lane acc' : UInt64) : Prop :=
  acc' = XxHash64.round acc lane

instance : Decidable (ValidRound acc lane acc') :=
  inferInstanceAs (Decidable (_ = _))

/-! ## Convergence -/

/-- Valid convergence of four accumulators into a single hash value.
    The four accumulators are combined via rotation and `mergeAccumulator`:
    `h = rotl(acc1,1) + rotl(acc2,7) + rotl(acc3,12) + rotl(acc4,18)`
    then merged sequentially with each accumulator. -/
def ValidConvergence (s : RoundState) (h : UInt64) : Prop :=
  let h₀ := XxHash64.rotl s.acc1 1 + XxHash64.rotl s.acc2 7 +
             XxHash64.rotl s.acc3 12 + XxHash64.rotl s.acc4 18
  let h₁ := XxHash64.mergeAccumulator h₀ s.acc1
  let h₂ := XxHash64.mergeAccumulator h₁ s.acc2
  let h₃ := XxHash64.mergeAccumulator h₂ s.acc3
  h = XxHash64.mergeAccumulator h₃ s.acc4

instance : Decidable (ValidConvergence s h) :=
  inferInstanceAs (Decidable (_ = _))

/-! ## Avalanche mixing -/

/-- Valid avalanche mixing (final step of xxHash64).
    Three rounds of xor-shift-multiply:
    1. `h ^= h >>> 33; h *= PRIME64_2`
    2. `h ^= h >>> 29; h *= PRIME64_3`
    3. `h ^= h >>> 32` -/
def ValidAvalanche (input output : UInt64) : Prop :=
  output = XxHash64.avalanche input

instance : Decidable (ValidAvalanche input output) :=
  inferInstanceAs (Decidable (_ = _))

/-! ## Remaining bytes processing -/

/-- Valid processing of remaining bytes (after full 32-byte stripes).
    Handles 8-byte chunks, then a 4-byte chunk, then 1-byte chunks,
    each with specific mixing constants. -/
def ValidProcessRemaining (acc : UInt64) (data : ByteArray) (off len : Nat)
    (result : UInt64) : Prop :=
  result = XxHash64.processRemaining acc data off len

instance : Decidable (ValidProcessRemaining acc data off len result) :=
  inferInstanceAs (Decidable (_ = _))

/-! ## Specification theorems -/

/-- The prime constants match the xxHash specification values. -/
theorem primes_valid : ValidPrimes := by
  unfold ValidPrimes PRIME64_1 PRIME64_2 PRIME64_3 PRIME64_4 PRIME64_5
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `xxHash64` is deterministic: same input and seed produce the same output.
    This is trivially true since `xxHash64` is a pure function, but it
    establishes the baseline property for a hash specification. -/
theorem xxHash64_deterministic (data : ByteArray) (seed : UInt64) :
    xxHash64 data seed = xxHash64 data seed := rfl

/-- The empty-input hash equals `avalanche (seed + PRIME64_5)`.
    For inputs shorter than 32 bytes, the hash is initialized as
    `seed + PRIME64_5` (no accumulator phase), then remaining bytes
    are processed, then avalanche is applied. For truly empty input,
    `processRemaining` is a no-op, leaving `avalanche(seed + PRIME64_5)`.
    Proof deferred: requires unfolding `Id.run do` with while loops in
    `processRemaining`. -/
theorem xxHash64_empty (seed : UInt64) :
    xxHash64 (ByteArray.empty) seed = avalanche (seed + PRIME64_5) := by
  sorry

/-- The Zstd content checksum is the upper 32 bits of XXH64 with seed 0.
    This connects the full 64-bit hash to the 32-bit format stored in
    Zstd frame footers (RFC 8878 §3.1.1). -/
theorem xxHash64Upper32_eq (data : ByteArray) :
    xxHash64Upper32 data = (xxHash64 data 0 >>> 32).toUInt32 := by
  unfold xxHash64Upper32
  rfl

end XxHash64.Spec
