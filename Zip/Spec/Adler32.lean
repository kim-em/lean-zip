/-!
# Adler-32 Specification

Adler-32 is a checksum defined in RFC 1950. It maintains two 16-bit sums
modulo 65521 (the largest prime less than 2^16):

  A = 1 + sum of all bytes
  B = sum of all A values after each byte

The result is `(B <<< 16) ||| A`, packed into a `UInt32`.

Characterizing property: compositionality of incremental computation
(see `PLAN.md:27-28`) — `checksum (xs ++ ys)` can be recovered from
`checksum xs` by unpacking its running state, feeding more bytes, then
re-packing. See `checksum_append` below.
-/

namespace Adler32.Spec

/-- The Adler-32 modulus: largest prime less than 2^16. -/
def MOD_ADLER : Nat := 65521

/-- The two components of an Adler-32 state: (A, B). -/
abbrev State := Nat × Nat

/-- Initial Adler-32 state: A = 1, B = 0. -/
def init : State := (1, 0)

/-- Process a single byte, updating the Adler-32 state. -/
def updateByte (s : State) (byte : UInt8) : State :=
  let a := (s.1 + byte.toNat) % MOD_ADLER
  let b := (s.2 + a) % MOD_ADLER
  (a, b)

/-- Process a list of bytes via left fold. -/
def updateList (s : State) (data : List UInt8) : State :=
  data.foldl updateByte s

/-- Pack the state into a `UInt32`: `(B <<< 16) ||| A`. -/
def pack (s : State) : UInt32 :=
  (UInt32.ofNat s.2 <<< 16) ||| UInt32.ofNat s.1

/-- Compute the Adler-32 checksum of a byte list. -/
def checksum (data : List UInt8) : UInt32 :=
  pack (updateList init data)

/-- Unpack a `UInt32` into Adler-32 state: `(A, B)`. -/
def unpack (v : UInt32) : State :=
  (v.toNat % 65536, v.toNat / 65536)

/-! ## Specification theorems -/

/-- `updateList` over a concatenation equals sequential application. -/
theorem updateList_append (s : State) (xs ys : List UInt8) :
    updateList s (xs ++ ys) = updateList (updateList s xs) ys := by
  simp only [updateList, List.foldl_append]

/-- Empty input leaves the state unchanged. -/
theorem updateList_nil (s : State) : updateList s [] = s := rfl

/-- Cons unfolds to updateByte then updateList. -/
theorem updateList_cons (s : State) (b : UInt8) (bs : List UInt8) :
    updateList s (b :: bs) = updateList (updateByte s b) bs := rfl

/-- The Adler-32 checksum of the empty input is `1`. -/
@[simp] theorem checksum_empty : checksum [] = 1 := by
  simp only [checksum, updateList_nil, pack, init]
  decide

/-! ## Bounds theorems -/

/-- A state is valid when both components are less than MOD_ADLER. -/
def Valid (s : State) : Prop := s.1 < MOD_ADLER ∧ s.2 < MOD_ADLER

/-- The first component of `updateByte` is less than MOD_ADLER. -/
theorem updateByte_fst_lt (s : State) (b : UInt8) :
    (updateByte s b).1 < MOD_ADLER := by
  simp only [updateByte, MOD_ADLER]
  omega

/-- The second component of `updateByte` is less than MOD_ADLER. -/
theorem updateByte_snd_lt (s : State) (b : UInt8) :
    (updateByte s b).2 < MOD_ADLER := by
  simp only [updateByte, MOD_ADLER]
  omega

/-- `updateByte` preserves validity. -/
theorem updateByte_valid (s : State) (b : UInt8) :
    Valid (updateByte s b) :=
  ⟨updateByte_fst_lt s b, updateByte_snd_lt s b⟩

/-- The initial state is valid. -/
theorem init_valid : Valid init := by
  simp only [Valid, init, MOD_ADLER]
  omega

/-- `updateList` preserves validity. -/
theorem updateList_valid (s : State) (hs : Valid s) (data : List UInt8) :
    Valid (updateList s data) := by
  induction data generalizing s with
  | nil => exact hs
  | cons b bs ih => exact ih (updateByte s b) (updateByte_valid s b)

/-! ## Compositionality -/

/-- `pack` applied to a valid state has `.toNat = s.1 + s.2 * 65536`
(the natural Nat-level view of the bitwise layout). -/
private theorem pack_toNat_of_bounds {a b : Nat} (ha : a < 65536) (hb : b < 65536) :
    (pack (a, b)).toNat = a + b * 65536 := by
  simp only [pack, UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt32.toNat_ofNat,
    UInt32.toNat_ofNat', Nat.shiftLeft_eq]
  have hpow : (2 : Nat) ^ (16 % 2 ^ 32 % 32) = 65536 := by decide
  rw [Nat.mod_eq_of_lt (show a < 2^32 by omega),
      Nat.mod_eq_of_lt (show b < 2^32 by omega), hpow,
      Nat.mod_eq_of_lt (show b * 65536 < 2^32 by
        have hsz : (2:Nat)^32 = 65536 * 65536 := by decide
        omega)]
  have hkey := Nat.two_pow_add_eq_or_of_lt (i := 16) (show a < 2^16 from ha) b
  have heq : b * 65536 = 2 ^ 16 * b := by
    show b * 65536 = 65536 * b
    exact Nat.mul_comm _ _
  rw [heq, ← hkey]
  omega

/-- The pack/unpack pair is a right-inverse: `pack ∘ unpack = id` on
any `UInt32`. The packed representation recovers the whole 32-bit
value because `unpack` splits it into the low 16 bits (first component)
and the high 16 bits (second component), and `pack` re-layers them. -/
theorem pack_unpack (v : UInt32) : pack (unpack v) = v := by
  rw [← UInt32.toNat_inj]
  have hmod_lt : v.toNat % 65536 < 65536 := Nat.mod_lt _ (by decide)
  have hdiv_lt : v.toNat / 65536 < 65536 := by
    rw [Nat.div_lt_iff_lt_mul (by decide : (0 : Nat) < 65536)]
    have hpow : (65536 : Nat) * 65536 = 2 ^ 32 := by decide
    have := v.toNat_lt
    omega
  simp only [unpack, pack_toNat_of_bounds hmod_lt hdiv_lt]
  have := Nat.div_add_mod v.toNat 65536
  omega

/-- `unpack ∘ pack` is the identity on `Valid` states. The pack/unpack
pair places `s.1` into the low 16 bits and `s.2` into the high 16 bits
of a `UInt32`; both components fit in 16 bits when `Valid`, so the
layering is lossless. -/
theorem unpack_pack_of_valid (s : State) (hs : Valid s) :
    unpack (pack s) = s := by
  obtain ⟨h1, h2⟩ := hs
  simp only [MOD_ADLER] at h1 h2
  obtain ⟨a, b⟩ := s
  simp only at h1 h2
  simp only [unpack, pack_toNat_of_bounds (show a < 65536 by omega) (show b < 65536 by omega),
    Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt (by omega)
  · rw [Nat.add_mul_div_right _ _ (by decide : (0 : Nat) < 65536)]
    simp [Nat.div_eq_of_lt (show a < 65536 by omega)]

/-- The Adler-32 checksum of a single byte `b` has the closed form
`(1 + b.toNat) * 65537`. Both Adler-32 components reduce to `1 + b.toNat`
because no modular reduction fires (`1 + b.toNat < 256 < 65521`), and
`pack (a, a) = a + a * 65536 = a * 65537` for `a < 65536`. -/
theorem checksum_singleton (b : UInt8) :
    checksum [b] = UInt32.ofNat ((1 + b.toNat) * 65537) := by
  have h256 : b.toNat < 256 := b.toNat_lt
  have hb : 1 + b.toNat < 65536 := by omega
  have ha : (1 + b.toNat) % 65521 = 1 + b.toNat := Nat.mod_eq_of_lt (by omega)
  have hbnd : (1 + b.toNat) * 65537 < UInt32.size := by
    simp only [UInt32.size]; omega
  rw [← UInt32.toNat_inj]
  simp only [checksum, updateList, List.foldl_cons, List.foldl_nil,
    updateByte, init, MOD_ADLER, Nat.zero_add, ha,
    pack_toNat_of_bounds hb hb, UInt32.toNat_ofNat_of_lt' hbnd]
  omega

/-- The Adler-32 checksum of a two-byte input `[b₁, b₂]` has the closed
form `(1 + b₁ + b₂) + (2 + 2·b₁ + b₂) * 65536` (as a `UInt32`). Both
state components stay well below `MOD_ADLER = 65521` after two updates
(max values `511` and `767`), so no modular reduction fires, and the
result is the unreduced packed pair. -/
theorem checksum_pair (b₁ b₂ : UInt8) :
    checksum [b₁, b₂] = UInt32.ofNat
      ((1 + b₁.toNat + b₂.toNat) +
       (2 + 2 * b₁.toNat + b₂.toNat) * 65536) := by
  have h1 : b₁.toNat < 256 := b₁.toNat_lt
  have h2 : b₂.toNat < 256 := b₂.toNat_lt
  rw [← UInt32.toNat_inj]
  simp only [checksum, updateList, List.foldl_cons, List.foldl_nil,
    updateByte, init, MOD_ADLER]
  have ha₁ : (1 + b₁.toNat) % 65521 = 1 + b₁.toNat :=
    Nat.mod_eq_of_lt (by omega)
  have ha₂ : (1 + b₁.toNat + b₂.toNat) % 65521 = 1 + b₁.toNat + b₂.toNat :=
    Nat.mod_eq_of_lt (by omega)
  have hb₂ : ((1 + b₁.toNat) + (1 + b₁.toNat + b₂.toNat)) % 65521 =
             (1 + b₁.toNat) + (1 + b₁.toNat + b₂.toNat) :=
    Nat.mod_eq_of_lt (by omega)
  rw [ha₁, Nat.zero_add, ha₁, ha₂, hb₂,
    pack_toNat_of_bounds (show 1 + b₁.toNat + b₂.toNat < 65536 by omega)
                          (show (1 + b₁.toNat) + (1 + b₁.toNat + b₂.toNat) < 65536 by omega),
    UInt32.toNat_ofNat_of_lt' (show (1 + b₁.toNat + b₂.toNat) +
        (2 + 2 * b₁.toNat + b₂.toNat) * 65536 < UInt32.size by
      simp only [UInt32.size]; omega)]
  omega

/-- Compositionality of incremental Adler-32 computation (spec level).
The running state after processing `xs` is `unpack (checksum xs)`;
feeding `ys` into that state and re-packing yields
`checksum (xs ++ ys)`. -/
theorem checksum_append (xs ys : List UInt8) :
    checksum (xs ++ ys) =
    pack (updateList (unpack (checksum xs)) ys) := by
  unfold checksum
  rw [updateList_append]
  rw [unpack_pack_of_valid _ (updateList_valid init init_valid xs)]

end Adler32.Spec
