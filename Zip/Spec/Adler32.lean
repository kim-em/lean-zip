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
  have ha₁ : (1 + b₁.toNat) % 65521 = 1 + b₁.toNat := Nat.mod_eq_of_lt (by omega)
  have ha₂ : (1 + b₁.toNat + b₂.toNat) % 65521 = 1 + b₁.toNat + b₂.toNat :=
    Nat.mod_eq_of_lt (by omega)
  have hb₂ : ((1 + b₁.toNat) + (1 + b₁.toNat + b₂.toNat)) % 65521 =
             (1 + b₁.toNat) + (1 + b₁.toNat + b₂.toNat) :=
    Nat.mod_eq_of_lt (by omega)
  have hpack₁ : 1 + b₁.toNat + b₂.toNat < 65536 := by omega
  have hpack₂ : (1 + b₁.toNat) + (1 + b₁.toNat + b₂.toNat) < 65536 := by omega
  have hbnd : (1 + b₁.toNat + b₂.toNat) +
      (2 + 2 * b₁.toNat + b₂.toNat) * 65536 < UInt32.size := by
    simp only [UInt32.size]; omega
  rw [← UInt32.toNat_inj]
  simp only [checksum, updateList, List.foldl_cons, List.foldl_nil,
    updateByte, init, MOD_ADLER, Nat.zero_add, ha₁, ha₂, hb₂,
    pack_toNat_of_bounds hpack₁ hpack₂,
    UInt32.toNat_ofNat_of_lt' hbnd]
  omega

/-- The Adler-32 checksum of `n` zero bytes has the closed form
`1 + n * 65536` (as a `UInt32`) when `n < 65521 = MOD_ADLER`. The
state after `n` updates with byte `0` starting from `init = (1, 0)`
is `(1, n)`, because the first component never changes (adding `0`
mod anything) and the second accumulates `1` per step. -/
theorem checksum_replicate_zero (n : Nat) (hn : n < 65521) :
    checksum (List.replicate n 0) = UInt32.ofNat (1 + n * 65536) := by
  have hstate : ∀ (m k : Nat), k + m < 65521 →
      updateList (1, k) (List.replicate m 0) = (1, k + m) := by
    intro m
    induction m with
    | zero => intros; rfl
    | succ m ih =>
      intro k hkm
      have hk1 : k + 1 < 65521 := by omega
      rw [List.replicate_succ, updateList_cons]
      simp only [updateByte, MOD_ADLER, show (0:UInt8).toNat = 0 from rfl,
        Nat.add_zero, show (1:Nat) % 65521 = 1 from rfl, Nat.mod_eq_of_lt hk1]
      rw [ih (k + 1) (by omega)]
      congr 1; omega
  have hupdate : updateList init (List.replicate n 0) = (1, n) := by
    simpa [init] using hstate n 0 (by omega)
  have hbnd : 1 + n * 65536 < UInt32.size := by
    simp only [UInt32.size]; omega
  rw [← UInt32.toNat_inj]
  simp only [checksum, hupdate,
    pack_toNat_of_bounds (show (1:Nat) < 65536 by omega) (show n < 65536 by omega),
    UInt32.toNat_ofNat_of_lt' hbnd]

/-- The Adler-32 checksum of `n` copies of byte `b` has the closed
form `(n + (n·(n+1)/2)·b) · 65536 + (1 + n·b)` (packed into a
`UInt32`) when both components stay below `65521`. The A-component
accumulates `n·b` and the B-component follows a triangular
progression because it sums consecutive A-values.
Generalizes `checksum_replicate_zero` (the `b = 0` case) and
provides the last arbitrary-byte closed form needed before the
ladder graduates to the append-based compositional theorem. -/
theorem checksum_replicate (n : Nat) (b : UInt8)
    (hA : 1 + n * b.toNat < 65521)
    (hB : n + (n * (n + 1) / 2) * b.toNat < 65521) :
    checksum (List.replicate n b) =
      UInt32.ofNat ((n + (n * (n + 1) / 2) * b.toNat) * 65536
                     + (1 + n * b.toNat)) := by
  -- Triangular-number recurrence `T_{k+1} = T_k + (k+1)`.
  have htri : ∀ (m : Nat), (m + 1) * (m + 2) / 2 = m * (m + 1) / 2 + (m + 1) := by
    intro m
    rw [show (m + 1) * (m + 2) = m * (m + 1) + (m + 1) * 2 by
          rw [Nat.mul_add (m + 1) m 2, Nat.mul_comm (m + 1) m],
        Nat.add_mul_div_right _ _ (by decide : 0 < 2)]
  -- Strengthened invariant, free over the starting `(a, bsum)`.
  have hstate : ∀ (m a bsum : Nat),
      a + m * b.toNat < 65521 →
      bsum + m * a + (m * (m + 1) / 2) * b.toNat < 65521 →
      updateList (a, bsum) (List.replicate m b) =
        (a + m * b.toNat, bsum + m * a + (m * (m + 1) / 2) * b.toNat) := by
    intro m
    induction m with
    | zero => intros; simp only [updateList, List.replicate, List.foldl_nil,
        Nat.zero_mul, Nat.zero_div, Nat.add_zero]
    | succ k ih =>
      intro a bsum ha hb
      -- Normalize `k + 1 + 1` → `k + 2` so omega sees matching atoms.
      change bsum + (k + 1) * a + ((k + 1) * (k + 2) / 2) * b.toNat < 65521 at hb
      show updateList (a, bsum) (List.replicate (k + 1) b) =
        (a + (k + 1) * b.toNat,
         bsum + (k + 1) * a + ((k + 1) * (k + 2) / 2) * b.toNat)
      -- Distributivity facts (omega treats `k*_`, `T_k*b`, `T_{k+1}*b` as atoms).
      have hka : (k + 1) * a = k * a + a := Nat.succ_mul k a
      have hkb : (k + 1) * b.toNat = k * b.toNat + b.toNat := Nat.succ_mul k b.toNat
      have hkab : k * (a + b.toNat) = k * a + k * b.toNat := Nat.mul_add k a b.toNat
      have hbtri : ((k + 1) * (k + 2) / 2) * b.toNat
                 = (k * (k + 1) / 2) * b.toNat + (k * b.toNat + b.toNat) := by
        rw [htri k, Nat.add_mul, Nat.succ_mul k b.toNat]
      rw [List.replicate_succ, updateList_cons]
      simp only [updateByte, MOD_ADLER,
        Nat.mod_eq_of_lt (show a + b.toNat < 65521 by omega),
        Nat.mod_eq_of_lt (show bsum + (a + b.toNat) < 65521 by omega)]
      rw [ih (a + b.toNat) (bsum + (a + b.toNat)) (by omega) (by omega)]
      refine Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩ <;> omega
  -- Instantiate at (1, 0) and n.
  have hupdate : updateList init (List.replicate n b) =
      (1 + n * b.toNat, n + (n * (n + 1) / 2) * b.toNat) := by
    have h := hstate n 1 0 hA (by omega)
    show updateList (1, 0) (List.replicate n b) = _
    rw [h]; refine Prod.mk.injEq .. |>.mpr ⟨rfl, ?_⟩; omega
  have hbnd : (n + (n * (n + 1) / 2) * b.toNat) * 65536
              + (1 + n * b.toNat) < UInt32.size := by
    simp only [UInt32.size]; omega
  rw [← UInt32.toNat_inj]
  simp only [checksum, hupdate,
    pack_toNat_of_bounds (show 1 + n * b.toNat < 65536 by omega)
      (show n + (n * (n + 1) / 2) * b.toNat < 65536 by omega),
    UInt32.toNat_ofNat_of_lt' hbnd]
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

/-! ## Combine: the two-block closed form -/

/-- Sum of a byte list as `Nat`. Internal helper for the combine lemma —
expresses the linear "s1"-delta produced by `updateList`. -/
private def sumBytes : List UInt8 → Nat
  | [] => 0
  | x :: xs => x.toNat + sumBytes xs

/-- Triangular-weighted sum: byte at index 0 is counted `xs.length` times,
the next byte `xs.length - 1` times, and so on. This is exactly the "s2"
increment produced by `updateList` started from `(0, 0)` (the s2 component
is `∑_{i=1..n} A_i` where `A_i = ∑_{j=1..i} bytes`). -/
private def triSum : List UInt8 → Nat
  | [] => 0
  | x :: xs => x.toNat * (xs.length + 1) + triSum xs

private theorem sumBytes_cons (x : UInt8) (xs : List UInt8) :
    sumBytes (x :: xs) = x.toNat + sumBytes xs := rfl

private theorem triSum_cons (x : UInt8) (xs : List UInt8) :
    triSum (x :: xs) = x.toNat * (xs.length + 1) + triSum xs := rfl

/-- Substituting `d` for `d % M` inside `(a + c * d) % M` is a no-op. -/
private theorem mod_subst_mul (a c d : Nat) :
    (a + c * (d % MOD_ADLER)) % MOD_ADLER = (a + c * d) % MOD_ADLER := by
  rw [Nat.add_mod, Nat.mul_mod_mod, ← Nat.add_mod]

/-- Like `mod_subst_mul`, with a trailing additive term. -/
private theorem mod_subst_mul_middle (a b c d : Nat) :
    (a + b * (c % MOD_ADLER) + d) % MOD_ADLER = (a + b * c + d) % MOD_ADLER := by
  rw [Nat.add_mod _ d MOD_ADLER, mod_subst_mul, ← Nat.add_mod]

/-- Extracting `(X % M)` appearing as the leading term of a chain of sums
followed by `% M`: `(X % M + Y + Z) % M = (X + Y + Z) % M`. -/
private theorem mod_absorb_leading (a b c : Nat) :
    (a % MOD_ADLER + b + c) % MOD_ADLER = (a + b + c) % MOD_ADLER := by
  rw [Nat.add_assoc, Nat.mod_add_mod, ← Nat.add_assoc]

/-- Separation formula for `updateList`: the state after processing `xs`
from starting state `(a, b)` is `((a + S) % M, (b + n·a + T) % M)`, where
`S = sumBytes xs`, `T = triSum xs`, `n = xs.length`, `M = MOD_ADLER`.
The lemma requires `a, b < M` so that the base case `updateList (a, b) []`
agrees with `(a % M, b % M)`. -/
private theorem updateList_separation (xs : List UInt8) :
    ∀ (a b : Nat), a < MOD_ADLER → b < MOD_ADLER →
      updateList (a, b) xs =
        ((a + sumBytes xs) % MOD_ADLER,
         (b + xs.length * a + triSum xs) % MOD_ADLER) := by
  induction xs with
  | nil =>
    intro a b ha hb
    simp only [updateList_nil, sumBytes, triSum, List.length_nil,
      Nat.zero_mul, Nat.add_zero]
    refine Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩
    · exact (Nat.mod_eq_of_lt ha).symm
    · exact (Nat.mod_eq_of_lt hb).symm
  | cons x xs ih =>
    intro a b ha hb
    have hsum_add : (a + x.toNat) % MOD_ADLER < MOD_ADLER :=
      Nat.mod_lt _ (by decide)
    have hb_upd : (b + (a + x.toNat) % MOD_ADLER) % MOD_ADLER < MOD_ADLER :=
      Nat.mod_lt _ (by decide)
    rw [updateList_cons, updateByte]
    rw [ih _ _ hsum_add hb_upd]
    refine Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩
    · -- First component: ((a + x) % M + S xs) % M = (a + (x + S xs)) % M
      simp only [sumBytes_cons, Nat.mod_add_mod]
      congr 1; omega
    · -- Second component: push all `% M` out of subterms, then algebra.
      simp only [triSum_cons, List.length_cons]
      -- Step 1: reduce `(b + (a + x) % M) % M` to `(b + (a + x)) % M` via `Nat.add_mod_mod`.
      rw [Nat.add_mod_mod]
      -- Step 2: extract the leading `(b + (a + x)) % M`, then substitute the inner
      -- `(a + x.toNat) % M` in `xs.length * ((a + x.toNat) % M)`.
      rw [mod_absorb_leading, mod_subst_mul_middle]
      congr 1
      have h1 : (xs.length + 1) * a = xs.length * a + a := Nat.succ_mul _ _
      have h2 : x.toNat * (xs.length + 1) = x.toNat * xs.length + x.toNat := by
        rw [Nat.mul_succ]
      have h3 : xs.length * (a + x.toNat) = xs.length * a + xs.length * x.toNat :=
        Nat.mul_add _ _ _
      have h4 : x.toNat * xs.length = xs.length * x.toNat := Nat.mul_comm _ _
      omega

/-- `updateList init xs` has its first component equal to
`(1 + sumBytes xs) % MOD_ADLER`. -/
private theorem updateList_init_fst (xs : List UInt8) :
    (updateList init xs).1 = (1 + sumBytes xs) % MOD_ADLER := by
  have h := updateList_separation xs 1 0 (by decide) (by decide)
  show (updateList (1, 0) xs).1 = _
  rw [h]

/-- `updateList init xs` has its second component equal to
`(xs.length + triSum xs) % MOD_ADLER`. -/
private theorem updateList_init_snd (xs : List UInt8) :
    (updateList init xs).2 = (xs.length + triSum xs) % MOD_ADLER := by
  have h := updateList_separation xs 1 0 (by decide) (by decide)
  show (updateList (1, 0) xs).2 = _
  rw [h]
  -- Goal: (0 + xs.length * 1 + triSum xs) % M = (xs.length + triSum xs) % M
  rw [show (0 + xs.length * 1 + triSum xs : Nat) = xs.length + triSum xs from by omega]

/-- State-level combine lemma: the state reached from starting point
`(a, b)` after processing `ys` can be expressed from the `(1, 0)`-chain
state `(b1, b2) = updateList init ys` and the length `n = ys.length`
alone. Each additive shift `+ MOD_ADLER - 1` and `+ n * MOD_ADLER - n`
keeps the arithmetic non-negative in `ℕ` (subtraction is saturating). -/
private theorem updateList_combine (ys : List UInt8) (a b : Nat)
    (ha : a < MOD_ADLER) (hb : b < MOD_ADLER) :
    let b1 := (updateList init ys).1
    let b2 := (updateList init ys).2
    let n := ys.length
    updateList (a, b) ys =
      ((a + b1 + MOD_ADLER - 1) % MOD_ADLER,
       (b + n * a + b2 + n * MOD_ADLER - n) % MOD_ADLER) := by
  simp only
  rw [updateList_separation ys a b ha hb]
  rw [updateList_init_fst ys, updateList_init_snd ys]
  refine Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩
  · -- Goal: (a + sumBytes ys) % M = (a + (1 + sumBytes ys) % M + M - 1) % M
    -- Rearrange: a + (1+S)%M + M - 1 = (a + M - 1) + (1+S)%M
    have hM : (1 : Nat) ≤ MOD_ADLER := by decide
    have hrearr : a + (1 + sumBytes ys) % MOD_ADLER + MOD_ADLER - 1
              = (a + MOD_ADLER - 1) + (1 + sumBytes ys) % MOD_ADLER := by omega
    rw [hrearr, Nat.add_mod_mod]
    have heq : (a + MOD_ADLER - 1) + (1 + sumBytes ys) = (a + sumBytes ys) + MOD_ADLER := by
      omega
    rw [heq, Nat.add_mod_right]
  · -- Goal: (b + n*a + T) % M = (b + n*a + (n + T) % M + n*M - n) % M, where n = ys.length
    have hnM : ys.length ≤ ys.length * MOD_ADLER := by
      calc ys.length = ys.length * 1 := (Nat.mul_one _).symm
           _ ≤ ys.length * MOD_ADLER :=
              Nat.mul_le_mul_left ys.length (by decide : 1 ≤ MOD_ADLER)
    have hrearr : b + ys.length * a + (ys.length + triSum ys) % MOD_ADLER
                + ys.length * MOD_ADLER - ys.length
              = (b + ys.length * a + ys.length * MOD_ADLER - ys.length)
                + (ys.length + triSum ys) % MOD_ADLER := by omega
    rw [hrearr, Nat.add_mod_mod]
    have heq : (b + ys.length * a + ys.length * MOD_ADLER - ys.length)
              + (ys.length + triSum ys)
              = (b + ys.length * a + triSum ys) + ys.length * MOD_ADLER := by omega
    rw [heq, Nat.add_mul_mod_self_right]

/-- Combine theorem: Adler-32 of a concatenation is a closed-form
function of the individual running states and the length of the
second block. This is the characterizing "combine" property used by
zlib's `adler32_combine` — it lets two parallel workers each hash a
block independently, then assemble the result without touching bytes.

The additive `+ MOD_ADLER - 1` and `+ n * MOD_ADLER - n` are Nat-safe
shifts of `- 1` and `- n` modulo `MOD_ADLER`. -/
theorem checksum_combine (xs ys : List UInt8) :
    let a1 := (updateList init xs).1
    let a2 := (updateList init xs).2
    let b1 := (updateList init ys).1
    let b2 := (updateList init ys).2
    let n := ys.length
    checksum (xs ++ ys) =
      pack ((a1 + b1 + MOD_ADLER - 1) % MOD_ADLER,
            (a2 + n * a1 + b2 + n * MOD_ADLER - n) % MOD_ADLER) := by
  have ⟨ha1, ha2⟩ : Valid (updateList init xs) :=
    updateList_valid init init_valid xs
  have hexp : checksum (xs ++ ys) =
      pack (updateList (updateList init xs) ys) := by
    unfold checksum; rw [updateList_append]
  have hcomb := updateList_combine ys (updateList init xs).1
    (updateList init xs).2 ha1 ha2
  simp only at hcomb ⊢
  rw [hexp]
  have hmk : updateList init xs =
      ((updateList init xs).1, (updateList init xs).2) := rfl
  rw [hmk, hcomb]

end Adler32.Spec
