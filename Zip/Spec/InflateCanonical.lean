import Zip.Spec.InflateTable
import Zip.Spec.HuffmanCorrectLoop

/-!
# Canonical O(n) decode-table build: equivalence to the tree-built table

`HuffTree.buildTableCanonical lengths` fills the fast decode table directly from
the code lengths (libdeflate `build_decode_table`): no Huffman tree, no per-slot
tree walk. The goal is to prove it equal to `buildTable (fromLengthsTree lengths)`,
so the canonical build becomes a drop-in for the tree-built table with every
decode proof transferring unchanged and no `@[implemented_by]` trust gap.

This file develops the format-independent **foundation** of that proof. The
planned route (per #2671) characterizes each table slot by the canonical code
table `allCodes`: slot `idx` holds `packEntry sym len` iff some `(sym, cw)` with
`len = cw.length ≤ fastBits` and `cwOf idx len = cw` is in `allCodes`, else the
sentinel `packEntry 0 0`. `buildTable`'s side follows from the existing
`hasLeaf_of_tableEntry_go` / `fromLengths_leaf_spec` / `fromLengths_hasLeaf`
bridge; the canonical loop's side from a table-local `nextCode` invariant. The
final equality theorem (`buildTableCanonical_eq`) and the decode rewiring land in
a follow-up; a differential conformance test already witnesses the equality at
runtime.

The foundation lemmas here, bottom-up:
1. `bitReverse` arithmetic — the bit-reversed codeword indexes the fast table.
2. `cwOf`/`bitReverse` bridge (`cwOf_eq_iff_mod`) — slot `idx` lies on a
   codeword's path iff `idx % 2^len` is the bit-reversed code.
3. `fillSlots` — what the slot-fill writes (`fillSlots_getElem_eq`) and
   preserves (`fillSlots_getElem_ne`, `fillSlots_size`).
-/

namespace Zip.Native.HuffTree

open Huffman.Spec (natToBits)

/-! ## `bitReverse` arithmetic -/

/-- The accumulator of `bitReverse` separates as a high-order summand: reversing
    `n` bits of `x` onto `acc` is `acc` shifted up by `n` plus the bare reversal. -/
theorem bitReverse_acc (x n acc : Nat) :
    bitReverse x n acc = acc * 2 ^ n + bitReverse x n 0 := by
  induction n generalizing x acc with
  | zero => simp [bitReverse]
  | succ n ih =>
    simp only [bitReverse]
    rw [ih (x / 2) (acc * 2 + x % 2), ih (x / 2) (0 * 2 + x % 2), Nat.zero_mul,
        Nat.zero_add, Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.add_mul,
        Nat.mul_assoc acc 2 (2 ^ n)]
    omega

/-- The bare reversal of `n` bits fits in `n` bits. -/
theorem bitReverse_lt (x n : Nat) : bitReverse x n 0 < 2 ^ n := by
  induction n generalizing x with
  | zero => simp [bitReverse]
  | succ n ih =>
    simp only [bitReverse]
    rw [bitReverse_acc, Nat.pow_succ]
    have hr := ih (x / 2)
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> omega

/-- Bit `i` (`i < n`) of the `n`-bit reversal of `x` is bit `n-1-i` of `x`:
    `bitReverse` reverses the low `n` bits. -/
theorem bitReverse_testBit (x n i : Nat) (hi : i < n) :
    (bitReverse x n 0).testBit i = x.testBit (n - 1 - i) := by
  induction n generalizing x i with
  | zero => omega
  | succ n ih =>
    have hR : bitReverse x (n + 1) 0 = 2 ^ n * (x % 2) + bitReverse (x / 2) n 0 := by
      simp only [bitReverse]
      rw [bitReverse_acc, Nat.zero_mul, Nat.zero_add, Nat.mul_comm (x % 2) (2 ^ n)]
    rw [hR, Nat.testBit_two_pow_mul_add _ (bitReverse_lt (x / 2) n)]
    rcases Nat.lt_or_ge i n with hlt | hge
    · rw [if_pos hlt, ih (x / 2) i hlt, ← Nat.testBit_succ]
      congr 1; omega
    · have hin : i = n := by omega
      subst hin
      rw [if_neg (by omega), Nat.sub_self, show i + 1 - 1 - i = 0 from by omega,
          Nat.testBit_zero, Nat.testBit_zero, show x % 2 % 2 = x % 2 from by omega]

/-! ## `cwOf` / `bitReverse` bridge

`tableEntry` walks the table index LSB-first, so slot `idx` lies on the path of a
length-`len` codeword `c` exactly when `cwOf idx len = natToBits c len`. The
canonical fill writes the slots `idx` with `idx % 2^len = bitReverse c len 0`;
these two descriptions coincide. -/

/-- `(natToBits c len)[j]` (MSB-first) is bit `len-1-j` of `c`. -/
theorem natToBits_getElem (c len j : Nat) (hj : j < len) :
    (natToBits c len)[j]'(by rw [Huffman.Spec.natToBits_length]; exact hj)
      = c.testBit (len - 1 - j) := by
  induction len generalizing j with
  | zero => omega
  | succ n ih =>
    match j with
    | 0 => simp only [natToBits, List.getElem_cons_zero, Nat.add_sub_cancel, Nat.sub_zero]
    | j + 1 =>
      have hstep : (natToBits c (n + 1))[j + 1]'(by rw [Huffman.Spec.natToBits_length]; omega)
          = (natToBits c n)[j]'(by rw [Huffman.Spec.natToBits_length]; omega) := by
        simp only [natToBits, List.getElem_cons_succ]
      rw [hstep, ih j (by omega)]; congr 1; omega

/-- `cwOf` depends only on the low `k` bits of `bits` (it reads them LSB-first). -/
theorem cwOf_mod (bits k : Nat) : cwOf (bits % 2 ^ k) k = cwOf bits k := by
  apply List.ext_getElem (by simp only [cwOf_length])
  intro j h₁ _
  rw [cwOf_length] at h₁
  rw [cwOf_getElem (bits % 2 ^ k) k j h₁, cwOf_getElem bits k j h₁,
      Nat.testBit_mod_two_pow]
  simp [h₁]

/-- The bit-reversed code is the unique low-`len`-bits value whose `cwOf` path is
    the codeword `natToBits c len`. -/
theorem cwOf_bitReverse (c len : Nat) :
    cwOf (bitReverse c len 0) len = natToBits c len := by
  apply List.ext_getElem (by rw [cwOf_length, Huffman.Spec.natToBits_length])
  intro j h₁ _
  rw [cwOf_length] at h₁
  rw [cwOf_getElem (bitReverse c len 0) len j h₁, bitReverse_testBit _ _ _ h₁,
      natToBits_getElem c len j h₁]

/-- Two `cwOf` paths of the same length agree iff the low bits agree. -/
theorem cwOf_mod_eq_of_cwOf_eq (a b len : Nat) (h : cwOf a len = cwOf b len) :
    a % 2 ^ len = b % 2 ^ len := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < len
  · simp only [hi, decide_true, Bool.true_and]
    have ha : (cwOf a len)[i]? = some (a.testBit i) := by
      rw [List.getElem?_eq_getElem (by rw [cwOf_length]; exact hi), cwOf_getElem a len i hi]
    have hb : (cwOf b len)[i]? = some (b.testBit i) := by
      rw [List.getElem?_eq_getElem (by rw [cwOf_length]; exact hi), cwOf_getElem b len i hi]
    rw [h, hb] at ha
    exact (Option.some.inj ha).symm
  · simp [hi]

/-- The slot-fill membership condition: slot `idx` lies on the path of a
    length-`len` codeword `c` (`cwOf idx len = natToBits c len`) iff its low
    `len` bits are the bit-reversed code. -/
theorem cwOf_eq_iff_mod (idx c len : Nat) :
    cwOf idx len = natToBits c len ↔ idx % 2 ^ len = bitReverse c len 0 := by
  constructor
  · intro h
    have h2 : cwOf (idx % 2 ^ len) len = cwOf (bitReverse c len 0) len := by
      rw [cwOf_mod, h, ← cwOf_bitReverse]
    have h3 := cwOf_mod_eq_of_cwOf_eq _ _ _ h2
    rwa [Nat.mod_eq_of_lt (Nat.mod_lt idx (Nat.two_pow_pos len)),
        Nat.mod_eq_of_lt (bitReverse_lt c len)] at h3
  · intro h
    have hbr := cwOf_bitReverse c len
    rw [← h] at hbr
    exact (cwOf_mod idx len).symm.trans hbr

/-! ## `fillSlots` -/

/-- `fillSlots` preserves the array size. -/
@[simp] theorem fillSlots_size (packed : Array UInt32) (base stride count : Nat)
    (entry : UInt32) :
    (fillSlots packed base stride count entry).size = packed.size := by
  induction count generalizing packed base with
  | zero => simp [fillSlots]
  | succ n ih =>
    rw [fillSlots]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [ih (packed.set! base entry) (base + stride)]
    simp

/-- A slot not on the fill's arithmetic progression `{base + j·stride : j < count}`
    keeps its old value. -/
theorem fillSlots_getElem_ne (packed : Array UInt32) (base stride count idx : Nat)
    (entry : UInt32) (h : ∀ j < count, idx ≠ base + j * stride) :
    (fillSlots packed base stride count entry)[idx]! = packed[idx]! := by
  induction count generalizing packed base with
  | zero => simp [fillSlots]
  | succ n ih =>
    rw [fillSlots]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [ih (packed.set! base entry) (base + stride) (by
      intro j hj
      have hne := h (j + 1) (by omega)
      have e : base + (j + 1) * stride = base + stride + j * stride := by
        rw [Nat.succ_mul]; omega
      rw [e] at hne; exact hne)]
    have hb : idx ≠ base := by have := h 0 (Nat.zero_lt_succ n); simpa using this
    rw [Array.set!_eq_setIfInBounds]
    by_cases hlt : idx < packed.size
    · rw [getElem!_pos _ idx (by rw [Array.size_setIfInBounds]; exact hlt),
          getElem!_pos _ idx hlt, Array.getElem_setIfInBounds hlt, if_neg (Ne.symm hb)]
    · rw [getElem!_neg _ idx (by rw [Array.size_setIfInBounds]; exact hlt),
          getElem!_neg _ idx hlt]

/-- A slot on the fill's arithmetic progression `base + j·stride` (`j < count`,
    in bounds) holds the fill value. -/
theorem fillSlots_getElem_eq (packed : Array UInt32) (base stride count j : Nat)
    (entry : UInt32) (hstride : 0 < stride) (hj : j < count)
    (hbound : base + j * stride < packed.size) :
    (fillSlots packed base stride count entry)[base + j * stride]! = entry := by
  induction count generalizing packed base j with
  | zero => omega
  | succ n ih =>
    rw [fillSlots]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    match j with
    | 0 =>
      rw [show base + 0 * stride = base from by omega]
      rw [fillSlots_getElem_ne (packed.set! base entry) (base + stride) stride n base entry
        (fun k _ => by omega)]
      have hbase : base < packed.size := by have := hbound; omega
      rw [Array.set!_eq_setIfInBounds,
          getElem!_pos _ base (by rw [Array.size_setIfInBounds]; exact hbase),
          Array.getElem_setIfInBounds_self]
    | j' + 1 =>
      have e : base + (j' + 1) * stride = base + stride + j' * stride := by
        rw [Nat.succ_mul]; omega
      rw [e]
      exact ih (packed.set! base entry) (base + stride) j' (by omega)
        (by rw [Array.size_set!, ← e]; exact hbound)

/-! ## `cwOf` prefix structure and fast-code uniqueness -/

/-- A shorter `cwOf` window is a prefix of a longer one over the same `idx`:
    both list the low bits of `idx` LSB-first, so `cwOf idx a` is the `a`-length
    prefix of `cwOf idx b` when `a ≤ b`. -/
theorem cwOf_prefix (idx a b : Nat) (hab : a ≤ b) :
    (cwOf idx a).IsPrefix (cwOf idx b) := by
  induction a generalizing idx b with
  | zero => simp only [cwOf]; exact List.nil_prefix
  | succ n ih =>
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    simp only [cwOf, List.cons_prefix_cons, true_and]
    exact ih (idx / 2) b' (by omega)

/-- A fast code present at table slot `idx`: a length-`≤ fastBits` canonical
    codeword whose `cwOf` path is `idx`'s low bits. -/
def FastCodeAt (lsList : List Nat) (maxBits idx k : Nat) (cw : List Bool) : Prop :=
  Huffman.Spec.codeFor lsList maxBits k = some cw ∧
    cw.length ≤ fastBits ∧ cwOf idx cw.length = cw

/-- At most one symbol's fast code matches a given slot: two matches would force
    one codeword to be a prefix of the other, contradicting prefix-freeness. -/
theorem fastCode_unique (lsList : List Nat) (maxBits idx : Nat)
    (hv : Huffman.Spec.ValidLengths lsList maxBits)
    (k₁ : Nat) (cw₁ : List Bool) (h₁ : FastCodeAt lsList maxBits idx k₁ cw₁)
    (k₂ : Nat) (cw₂ : List Bool) (h₂ : FastCodeAt lsList maxBits idx k₂ cw₂) :
    k₁ = k₂ := by
  obtain ⟨hcf₁, _, hcw₁⟩ := h₁
  obtain ⟨hcf₂, _, hcw₂⟩ := h₂
  refine Decidable.by_contra (fun hne => ?_)
  rcases Nat.le_total cw₁.length cw₂.length with hle | hle
  · have hpre : cw₁.IsPrefix cw₂ := by
      have := cwOf_prefix idx cw₁.length cw₂.length hle
      rwa [hcw₁, hcw₂] at this
    exact Huffman.Spec.canonical_prefix_free lsList maxBits hv k₁ k₂ cw₁ cw₂ hcf₁ hcf₂ hne hpre
  · have hpre : cw₂.IsPrefix cw₁ := by
      have := cwOf_prefix idx cw₂.length cw₁.length hle
      rwa [hcw₂, hcw₁] at this
    exact Huffman.Spec.canonical_prefix_free lsList maxBits hv k₂ k₁ cw₂ cw₁ hcf₂ hcf₁
      (Ne.symm hne) hpre

/-! ## Backward tree-walk lemma: a leaf on `cwOf`'s path is what `tableEntry` reads -/

/-- **Backward direction of `hasLeaf_of_tableEntry_go`.** If the tree has a leaf
    with symbol `sym` at the path `cwOf bits len` and the leaf is within the
    `fastBits` window from `depth`, then `tableEntry.go` walking `bits` from
    `depth` reaches exactly that `(sym, depth + len)`. -/
theorem tableEntry_go_of_hasLeaf (t : HuffTree) (bits depth len : Nat) (sym : UInt16)
    (h : Deflate.Correctness.TreeHasLeaf t (cwOf bits len) sym)
    (hd : depth + len ≤ fastBits) :
    tableEntry.go t bits depth = (sym, (depth + len).toUInt8) := by
  induction len generalizing t bits depth with
  | zero =>
    simp only [cwOf] at h
    cases h
    simp only [tableEntry.go, Nat.add_zero]
  | succ n ih =>
    rw [cwOf] at h
    cases t with
    | leaf s => nomatch h
    | empty => nomatch h
    | node z o =>
      rw [tableEntry.go, if_neg (show ¬ depth ≥ fastBits by omega),
        show depth + (n + 1) = (depth + 1) + n from by omega]
      split
      · rename_i hbit
        have hb0 : bits % 2 = 0 := by simpa using hbit
        rw [show (bits % 2 == 1) = false from by simp [hb0]] at h
        cases h with
        | left hz => exact ih z (bits / 2) (depth + 1) hz (by omega)
      · rename_i hbit
        have hb1 : bits % 2 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one bits with hh | hh
          · simp [hh] at hbit
          · exact hh
        rw [show (bits % 2 == 1) = true from by simp [hb1]] at h
        cases h with
        | right ho => exact ih o (bits / 2) (depth + 1) ho (by omega)

/-! ## The constructed tree is never a bare leaf -/

/-- A tree that is not a bare `leaf` (so `tableEntry.go` from depth 0 never reads
    a length-0 real entry). -/
def NotLeaf : HuffTree → Prop
  | .leaf _ => False
  | _ => True

/-- Inserting a positive-length code into a non-leaf tree yields a node. -/
theorem insert_go_notLeaf (code : UInt32) (sym : UInt16) (tree : HuffTree) (len : Nat)
    (hlen : 0 < len) (hnl : NotLeaf tree) :
    NotLeaf (HuffTree.insert.go code sym tree len) := by
  obtain ⟨n, rfl⟩ : ∃ n, len = n + 1 := ⟨len - 1, by omega⟩
  unfold HuffTree.insert.go
  cases tree with
  | empty => dsimp only; split <;> simp only [NotLeaf]
  | node z o => dsimp only; split <;> simp only [NotLeaf]
  | leaf s => exact hnl

/-- `insertLoop` preserves `NotLeaf`: starting from a non-leaf tree, the final
    tree is non-leaf (every inserted code has positive length). -/
theorem insertLoop_notLeaf (lengths : Array UInt8) (nextCode : Array UInt32)
    (start : Nat) (tree : HuffTree) (hnl : NotLeaf tree) :
    NotLeaf (HuffTree.insertLoop lengths nextCode start tree).1 := by
  unfold HuffTree.insertLoop
  split
  · rename_i hstart
    dsimp only []
    split
    · rename_i hlen_pos
      split
      · rename_i hlt
        exact insertLoop_notLeaf lengths _ (start + 1) _
          (insert_go_notLeaf _ _ tree _ hlen_pos hnl)
      · exact insertLoop_notLeaf lengths nextCode (start + 1) tree hnl
    · exact insertLoop_notLeaf lengths nextCode (start + 1) tree hnl
  · exact hnl
termination_by lengths.size - start

/-- The canonical Huffman tree is never a bare leaf. -/
theorem fromLengthsTree_notLeaf (lengths : Array UInt8) (maxBits : Nat) :
    NotLeaf (HuffTree.fromLengthsTree lengths maxBits) := by
  unfold HuffTree.fromLengthsTree
  exact insertLoop_notLeaf _ _ 0 .empty trivial

/-- For a non-leaf tree (or any `depth > 0`), a `tableEntry.go` result with a
    zero length byte is the full sentinel `(0, 0)`: the only real entries have
    positive depth, and depth never reaches 256 within the `fastBits` window. -/
theorem tableEntry_go_len_zero (t : HuffTree) :
    ∀ (bits depth : Nat), (0 < depth ∨ NotLeaf t) → depth ≤ fastBits →
    (tableEntry.go t bits depth).2.toNat = 0 → tableEntry.go t bits depth = (0, 0) := by
  induction t with
  | leaf s =>
    intro bits depth hdepth hdle h
    exfalso
    simp only [tableEntry.go] at h
    have h1 : (depth.toUInt8).toNat = depth % 256 := by
      simp only [Nat.toUInt8, UInt8.ofNat, UInt8.toNat, BitVec.toNat_ofNat, Nat.reducePow]
    rw [h1] at h
    rcases hdepth with hd | hd
    · simp only [fastBits] at hdle; omega
    · exact hd
  | empty => intro bits depth _ _ _; rfl
  | node z o ihz iho =>
    intro bits depth _ hdle h
    rw [tableEntry.go]
    rw [tableEntry.go] at h
    by_cases hge : depth ≥ fastBits
    · rw [if_pos hge]
    · rw [if_neg hge]; rw [if_neg hge] at h
      have hd' : depth + 1 ≤ fastBits := by simp only [fastBits] at hge ⊢; omega
      split
      · rename_i hbit
        rw [if_pos hbit] at h
        exact ihz (bits / 2) (depth + 1) (Or.inl (by omega)) hd' h
      · rename_i hbit
        rw [if_neg hbit] at h
        exact iho (bits / 2) (depth + 1) (Or.inl (by omega)) hd' h

/-! ## `fromLengths` succeeds under `ValidLengths` -/

/-- Under `ValidLengths`, `fromLengths` returns the canonical tree without error:
    the length-bound and Kraft checks are exactly the `ValidLengths` conjuncts. -/
theorem fromLengths_ok_of_valid (lengths : Array UInt8) (maxBits : Nat)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits) :
    HuffTree.fromLengths lengths maxBits = .ok (HuffTree.fromLengthsTree lengths maxBits) := by
  unfold HuffTree.fromLengths
  split
  · -- length-bound check would fail: contradicts `ValidLengths.1`.
    rename_i hany
    exfalso
    rw [Array.any_eq_true] at hany
    obtain ⟨i, hi, hp⟩ := hany
    simp only [decide_eq_true_eq] at hp
    have := hv.1 _ (List.mem_map.mpr ⟨lengths[i], Array.getElem_mem_toList .., rfl⟩)
    omega
  · dsimp only []
    split
    · -- Kraft check would fail: contradicts `ValidLengths.2`.
      rename_i hkraft
      exfalso
      simp only [gt_iff_lt] at hkraft
      have := hv.2
      omega
    · rfl

/-! ## `fillSlots` over a codeword's slot progression -/

/-- A slot whose low `len` bits are the fill `base` lies on the progression and
    holds the fill value. -/
theorem fillSlots_match (packed : Array UInt32) (base len fastB idx : Nat) (entry : UInt32)
    (hlen : len ≤ fastB) (_hbase : base < 2 ^ len) (hsize : packed.size = 2 ^ fastB)
    (hidx : idx < 2 ^ fastB) (hmod : idx % 2 ^ len = base) :
    (fillSlots packed base (2 ^ len) (2 ^ (fastB - len)) entry)[idx]! = entry := by
  have hj : idx / 2 ^ len < 2 ^ (fastB - len) := by
    apply Nat.div_lt_of_lt_mul; rw [← Nat.pow_add, Nat.add_sub_cancel' hlen]; exact hidx
  have hdm := Nat.div_add_mod idx (2 ^ len)
  rw [hmod] at hdm
  have hidx_eq : idx = base + (idx / 2 ^ len) * 2 ^ len := by
    rw [Nat.mul_comm (idx / 2 ^ len) (2 ^ len)]; omega
  rw [hidx_eq]
  exact fillSlots_getElem_eq packed base (2 ^ len) (2 ^ (fastB - len)) (idx / 2 ^ len) entry
    (Nat.two_pow_pos len) hj (by rw [← hidx_eq, hsize]; exact hidx)

/-- A slot whose low `len` bits differ from the fill `base` is untouched by the fill. -/
theorem fillSlots_nomatch (packed : Array UInt32) (base len count idx : Nat) (entry : UInt32)
    (hbase : base < 2 ^ len) (hmod : idx % 2 ^ len ≠ base) :
    (fillSlots packed base (2 ^ len) count entry)[idx]! = packed[idx]! := by
  apply fillSlots_getElem_ne
  intro j _ heq
  apply hmod
  rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hbase]

/-! ## `buildCanonicalLoop` preserves the table size -/

/-- The canonical fill loop never changes the table length (every write is an
    in-bounds `fillSlots`/`set!`). -/
theorem buildCanonicalLoop_size (lengths : Array UInt8) (nextCode : Array UInt32)
    (start : Nat) (packed : Array UInt32) :
    (buildCanonicalLoop lengths nextCode start packed).size = packed.size := by
  unfold buildCanonicalLoop
  split
  · dsimp only []
    split
    · split
      · rw [buildCanonicalLoop_size, fillSlots_size]
      · rw [buildCanonicalLoop_size]
    · rw [buildCanonicalLoop_size]
  · rfl
termination_by lengths.size - start

/-! ## Tree-side slot characterization -/

/-- **Tree side, matching slot.** If `(s, cw)` is a fast canonical code whose
    `cwOf` path is slot `idx`, then `buildTable`'s slot holds `packEntry s len`. -/
theorem treeSlot_match (lengths : Array UInt8) (maxBits : Nat) (hmb : maxBits < 32)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (s : Nat) (cw : List Bool) (idx : Nat) (hidx : idx < 2 ^ fastBits)
    (hmem : (s, cw) ∈ Huffman.Spec.allCodes (lengths.toList.map UInt8.toNat) maxBits)
    (hlen : cw.length ≤ fastBits) (hcw : cwOf idx cw.length = cw) :
    (HuffTree.buildTable (HuffTree.fromLengthsTree lengths maxBits)).packed[idx]!
      = packEntry s.toUInt16 cw.length.toUInt8 := by
  have htree := fromLengths_ok_of_valid lengths maxBits hv
  have hleaf : Deflate.Correctness.TreeHasLeaf (HuffTree.fromLengthsTree lengths maxBits)
      (cwOf idx cw.length) s.toUInt16 := by
    rw [hcw]; exact Deflate.Correctness.fromLengths_hasLeaf lengths maxBits hmb _ htree hv s cw hmem
  rw [buildTable_packed_getElem _ idx hidx,
    show HuffTree.tableEntry (HuffTree.fromLengthsTree lengths maxBits) idx
      = HuffTree.tableEntry.go (HuffTree.fromLengthsTree lengths maxBits) idx 0 from rfl,
    tableEntry_go_of_hasLeaf _ idx 0 cw.length s.toUInt16 hleaf (by simp only [Nat.zero_add]; exact hlen)]
  simp only [Nat.zero_add]

/-- **Tree side, sentinel slot.** If no fast canonical code's path is slot `idx`,
    then `buildTable`'s slot is the sentinel `packEntry 0 0`. -/
theorem treeSlot_sentinel (lengths : Array UInt8) (maxBits : Nat) (hmb : maxBits < 32)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (hbound : lengths.size ≤ UInt16.size)
    (idx : Nat) (hidx : idx < 2 ^ fastBits)
    (hno : ¬ ∃ s cw, (s, cw) ∈ Huffman.Spec.allCodes (lengths.toList.map UInt8.toNat) maxBits ∧
      cw.length ≤ fastBits ∧ cwOf idx cw.length = cw) :
    (HuffTree.buildTable (HuffTree.fromLengthsTree lengths maxBits)).packed[idx]! = packEntry 0 0 := by
  have htree := fromLengths_ok_of_valid lengths maxBits hv
  rw [buildTable_packed_getElem _ idx hidx]
  have hfin : HuffTree.tableEntry (HuffTree.fromLengthsTree lengths maxBits) idx = (0, 0) := by
    by_cases hlen0 : (HuffTree.tableEntry (HuffTree.fromLengthsTree lengths maxBits) idx).2.toNat = 0
    · exact tableEntry_go_len_zero _ idx 0 (Or.inr (fromLengthsTree_notLeaf lengths maxBits))
        (by simp only [fastBits]; omega) hlen0
    · exfalso
      have hgo : HuffTree.tableEntry.go (HuffTree.fromLengthsTree lengths maxBits) idx 0
          = ((HuffTree.tableEntry (HuffTree.fromLengthsTree lengths maxBits) idx).1,
             (HuffTree.tableEntry (HuffTree.fromLengthsTree lengths maxBits) idx).2) := rfl
      have hpos : 0 < (HuffTree.tableEntry (HuffTree.fromLengthsTree lengths maxBits) idx).2.toNat := by
        omega
      have hlenfast := tableEntry_go_len_le _ idx 0 _ _ hgo (by simp only [fastBits]; omega) hpos
      have hleaf := hasLeaf_of_tableEntry_go _ idx 0 _ _ hgo hlenfast hpos (by omega)
      rw [Nat.sub_zero] at hleaf
      have hspec := Deflate.Correctness.fromLengths_leaf_spec lengths maxBits hmb _ htree hv hbound
        (cwOf idx (HuffTree.tableEntry (HuffTree.fromLengthsTree lengths maxBits) idx).2.toNat) _ hleaf
      exact hno ⟨_, _, hspec, by rw [cwOf_length]; exact hlenfast, by rw [cwOf_length]⟩
  rw [hfin]

/-! ## Canonical-side slot characterization (the fill loop invariant) -/

/-- **The canonical fill loop's table-local invariant.** Carrying the `nextCode`
    (NC) invariant and a description of which slots `packed` already reflects
    (codes of symbols `< start`), the loop's result reflects *every* fast code:
    a slot holds `packEntry k len` exactly when symbol `k`'s fast canonical code
    lands there, and the sentinel otherwise. Single-slot (`idx` fixed) so the
    fill `if`s split cleanly. -/
theorem buildCanonicalLoop_spec
    (lengths : Array UInt8) (nextCode : Array UInt32) (start : Nat) (packed : Array UInt32)
    (lsList : List Nat) (hlsList : lsList = lengths.toList.map UInt8.toNat)
    (maxBits : Nat) (hmb : maxBits < 32)
    (blCount : Array Nat) (hblCount : blCount = Huffman.Spec.countLengths lsList maxBits)
    (ncSpec : Array Nat) (hncSpec : ncSpec = Huffman.Spec.nextCodes blCount maxBits)
    (hv : Huffman.Spec.ValidLengths lsList maxBits)
    (hncSize : nextCode.size = maxBits + 1) (hpsize : packed.size = 2 ^ fastBits)
    (idx : Nat) (hidx : idx < 2 ^ fastBits)
    (hnc : ∀ b, 1 ≤ b → b ≤ maxBits →
      nextCode[b]!.toNat = ncSpec[b]! +
        (lsList.take start).foldl (fun acc l => if l == b then acc + 1 else acc) 0)
    (hpre_sent : (¬ ∃ k cw, k < start ∧ FastCodeAt lsList maxBits idx k cw) →
      packed[idx]! = packEntry 0 0)
    (hpre_fill : ∀ k cw, k < start → FastCodeAt lsList maxBits idx k cw →
      packed[idx]! = packEntry k.toUInt16 cw.length.toUInt8) :
    ((¬ ∃ k cw, FastCodeAt lsList maxBits idx k cw) →
        (buildCanonicalLoop lengths nextCode start packed)[idx]! = packEntry 0 0) ∧
    (∀ k cw, FastCodeAt lsList maxBits idx k cw →
        (buildCanonicalLoop lengths nextCode start packed)[idx]!
          = packEntry k.toUInt16 cw.length.toUInt8) := by
  unfold buildCanonicalLoop
  split
  · rename_i hstart
    dsimp only []
    have hls_len : start < lsList.length := by
      rw [hlsList, List.length_map, Array.length_toList]; exact hstart
    have hls_start : lsList[start] = lengths[start].toNat := by
      simp only [hlsList, List.getElem_map, Array.getElem_toList]
    split
    · -- positive length in range: read code, possibly fill
      rename_i hcond
      have hlen_le : lengths[start].toNat ≤ maxBits := by
        rw [← hls_start]; exact hv.1 _ (List.getElem_mem hls_len)
      obtain ⟨cw_s, hcf_s⟩ := Deflate.Correctness.codeFor_some lsList maxBits start hls_len
        (by rw [hls_start]; omega) (by rw [hls_start]; omega)
      have hc! : (nextCode[lengths[start].toNat]'hcond.2) = nextCode[lengths[start].toNat]! :=
        getElem!_pos nextCode _ hcond.2 |>.symm
      have hcw_s : cw_s = Huffman.Spec.natToBits
          (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat := by
        obtain ⟨_, _, hcw⟩ := Huffman.Spec.codeFor_spec hcf_s
        rw [hcw, hls_start]; congr 1
        rw [← hblCount, ← hncSpec]
        exact (hnc lengths[start].toNat (by omega) hlen_le).symm
      have hcwlen : cw_s.length = lengths[start].toNat := by rw [hcw_s, Huffman.Spec.natToBits_length]
      -- matching slot ↔ low bits are the bit-reversed code
      have hmatch_iff : cwOf idx lengths[start].toNat = cw_s ↔
          idx % 2 ^ lengths[start].toNat
            = bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0 := by
        rw [hcw_s]; exact cwOf_eq_iff_mod idx _ _
      have hbase_lt : bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0
          < 2 ^ lengths[start].toNat := bitReverse_lt _ _
      have hnc' := Deflate.Correctness.nc_invariant_step lengths nextCode start lsList maxBits
        blCount hblCount ncSpec hncSpec hv hmb (by omega) hstart hls_len hls_start hlen_le hcond.1 hnc
      have hncSize' : (nextCode.set! lengths[start].toNat
          (nextCode[lengths[start].toNat]! + 1)).size = maxBits + 1 := by
        rw [Array.size_set!]; exact hncSize
      split
      · -- len ≤ fastBits: fill this code's slots
        rename_i hfast
        simp only [hc!]
        refine buildCanonicalLoop_spec lengths _ (start + 1) _ lsList hlsList maxBits hmb
          blCount hblCount ncSpec hncSpec hv hncSize' (by rw [fillSlots_size]; exact hpsize)
          idx hidx hnc' ?_ ?_
        · -- sentinel precondition at start+1
          intro hno
          have hidx_ne : idx % 2 ^ lengths[start].toNat
              ≠ bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0 := by
            intro hmod
            exact hno ⟨start, cw_s, by omega,
              hcf_s, by rw [hcwlen]; exact hfast, by rw [hcwlen, hmatch_iff]; exact hmod⟩
          rw [fillSlots_nomatch _ _ _ _ _ _ hbase_lt hidx_ne]
          exact hpre_sent (fun ⟨k, cw, hk, h⟩ => hno ⟨k, cw, by omega, h⟩)
        · -- fill precondition at start+1
          intro k cw hk hfca
          by_cases hks : k = start
          · subst hks
            have hcweq : cw = cw_s := Option.some.inj (hfca.1.symm.trans hcf_s)
            have hmod : idx % 2 ^ lengths[k].toNat
                = bitReverse (nextCode[lengths[k].toNat]!).toNat lengths[k].toNat 0 := by
              rw [← hmatch_iff]
              have hc22 := hfca.2.2
              rw [hcweq, hcwlen] at hc22; exact hc22
            rw [fillSlots_match _ _ _ _ _ _ hfast hbase_lt hpsize hidx hmod, hcweq, hcwlen]
            congr 1; exact UInt8.ofNat_toNat.symm
          · have hk' : k < start := by omega
            have hidx_ne : idx % 2 ^ lengths[start].toNat
                ≠ bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0 := by
              intro hmod
              have hfca_s : FastCodeAt lsList maxBits idx start cw_s :=
                ⟨hcf_s, by rw [hcwlen]; exact hfast, by rw [hcwlen, hmatch_iff]; exact hmod⟩
              exact hks (fastCode_unique lsList maxBits idx hv k cw hfca start cw_s hfca_s)
            rw [fillSlots_nomatch _ _ _ _ _ _ hbase_lt hidx_ne]
            exact hpre_fill k cw hk' hfca
      · -- len > fastBits: no fill, but nextCode advances
        rename_i hslow
        simp only [hc!]
        refine buildCanonicalLoop_spec lengths _ (start + 1) packed lsList hlsList maxBits hmb
          blCount hblCount ncSpec hncSpec hv hncSize' hpsize idx hidx hnc' ?_ ?_
        · intro hno
          exact hpre_sent (fun ⟨k, cw, hk, h⟩ => hno ⟨k, cw, by omega, h⟩)
        · intro k cw hk hfca
          have hks : k ≠ start := by
            rintro rfl
            have hcweq : cw = cw_s := Option.some.inj (hfca.1.symm.trans hcf_s)
            have hcl := hfca.2.1
            rw [hcweq, hcwlen] at hcl; omega
          exact hpre_fill k cw (by omega) hfca
    · -- length 0 (or out of range, impossible here): skip
      rename_i hcond
      have hlen0 : lengths[start].toNat = 0 := by
        rcases Nat.eq_zero_or_pos lengths[start].toNat with h | h
        · exact h
        · refine absurd ⟨h, ?_⟩ hcond
          rw [hncSize]
          have hle : lengths[start].toNat ≤ maxBits := by
            rw [← hls_start]; exact hv.1 _ (List.getElem_mem hls_len)
          omega
      have hls_val0 : lsList[start] = 0 := by rw [hls_start]; exact hlen0
      have hcf_none : Huffman.Spec.codeFor lsList maxBits start = none := by
        simp only [Huffman.Spec.codeFor, hls_len, ↓reduceDIte, hls_val0,
          beq_self_eq_true, Bool.true_or, ↓reduceIte]
      have hnc' := Deflate.Correctness.nc_invariant_skip nextCode start lsList maxBits ncSpec
        hls_len hls_val0 hnc
      refine buildCanonicalLoop_spec lengths nextCode (start + 1) packed lsList hlsList maxBits hmb
        blCount hblCount ncSpec hncSpec hv hncSize hpsize idx hidx hnc' ?_ ?_
      · intro hno
        exact hpre_sent (fun ⟨k, cw, hk, h⟩ => hno ⟨k, cw, by omega, h⟩)
      · intro k cw hk hfca
        have hks : k ≠ start := by
          rintro rfl
          have hcf := hfca.1
          rw [hcf_none] at hcf
          simp at hcf
        exact hpre_fill k cw (by omega) hfca
  · -- start ≥ lengths.size: base case, result = packed
    rename_i hstart
    have hlen_eq : lsList.length = lengths.size := by
      rw [hlsList, List.length_map, Array.length_toList]
    refine ⟨fun hno => hpre_sent (fun ⟨k, cw, _, h⟩ => hno ⟨k, cw, h⟩), fun k cw hfca => ?_⟩
    obtain ⟨hks, _, _⟩ := Huffman.Spec.codeFor_spec hfca.1
    exact hpre_fill k cw (by omega) hfca
termination_by lengths.size - start

/-- The initial `nextCode` array (`ncSpec.map (·.toUInt32)`) satisfies the NC
    invariant at `start = 0`: each entry's `toNat` equals the spec value (the
    map roundtrips because `ncSpec[b] < 2^maxBits ≤ 2^31` by Kraft). A local copy
    of `HuffmanCorrectLoop.initial_nc_invariant` (which is `private` there). -/
theorem canon_initial_nc_invariant (lengths : Array UInt8)
    (maxBits : Nat) (hmb : maxBits < 32)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (b : Nat) (hb1 : 1 ≤ b) (hb15 : b ≤ maxBits) :
    ((Huffman.Spec.nextCodes (Huffman.Spec.countLengths
        (lengths.toList.map UInt8.toNat) maxBits) maxBits).map
      Nat.toUInt32)[b]!.toNat =
    (Huffman.Spec.nextCodes (Huffman.Spec.countLengths
        (lengths.toList.map UInt8.toNat) maxBits) maxBits)[b]! := by
  have hbs : b < (Huffman.Spec.nextCodes (Huffman.Spec.countLengths
      (List.map UInt8.toNat lengths.toList) maxBits) maxBits).size := by
    rw [Huffman.Spec.nextCodes_size]; omega
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
             Array.getElem?_map, Array.getElem?_eq_getElem hbs,
             Option.map_some, Option.getD_some]
  have h_npc := Huffman.Spec.nextCodes_plus_count_le
    (List.map UInt8.toNat lengths.toList) maxBits b hv (by omega) hb15
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
             Array.getElem?_eq_getElem hbs, Option.getD_some] at h_npc
  have h_pow := Nat.pow_le_pow_right (by omega : 0 < 2) (show b ≤ 31 from by omega)
  show (Huffman.Spec.nextCodes _ maxBits)[b].toUInt32.toNat =
       (Huffman.Spec.nextCodes _ maxBits)[b]
  rw [show ∀ n : Nat, n.toUInt32.toNat = n % 2 ^ 32 from fun _ => rfl,
      Nat.mod_eq_of_lt (by omega)]

/-! ## The canonical build equals the tree build -/

/-- Each slot of the canonical build matches the tree build, by the
    `allCodes`-pointwise case split: a matching fast code makes both sides
    `packEntry s len`, no match makes both the sentinel. -/
theorem buildTableCanonical_packed_getElem (lengths : Array UInt8) (maxBits : Nat)
    (hmb : maxBits < 32)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (hbound : lengths.size ≤ UInt16.size)
    (idx : Nat) (hidx : idx < 2 ^ fastBits) :
    (HuffTree.buildTableCanonical lengths maxBits).packed[idx]!
      = (HuffTree.buildTable (HuffTree.fromLengthsTree lengths maxBits)).packed[idx]! := by
  -- canonical packed reduced to the fill loop
  have hcanon : (HuffTree.buildTableCanonical lengths maxBits).packed
      = buildCanonicalLoop lengths
          ((Huffman.Spec.nextCodes
            (Huffman.Spec.countLengths (lengths.toList.map UInt8.toNat) maxBits) maxBits).map
            Nat.toUInt32) 0 (Array.replicate (2 ^ fastBits) (packEntry 0 0)) := rfl
  have spec := buildCanonicalLoop_spec lengths
    ((Huffman.Spec.nextCodes
      (Huffman.Spec.countLengths (lengths.toList.map UInt8.toNat) maxBits) maxBits).map Nat.toUInt32)
    0 (Array.replicate (2 ^ fastBits) (packEntry 0 0)) (lengths.toList.map UInt8.toNat) rfl maxBits hmb
    (Huffman.Spec.countLengths (lengths.toList.map UInt8.toNat) maxBits) rfl
    (Huffman.Spec.nextCodes (Huffman.Spec.countLengths (lengths.toList.map UInt8.toNat) maxBits) maxBits)
    rfl hv
    (by rw [Array.size_map, Huffman.Spec.nextCodes_size])
    (by rw [Array.size_replicate]) idx hidx
    (by intro b hb1 hb15
        simp only [List.take_zero, List.foldl_nil, Nat.add_zero]
        exact canon_initial_nc_invariant lengths maxBits hmb hv b hb1 hb15)
    (fun _ => by rw [getElem!_pos _ idx (by rw [Array.size_replicate]; exact hidx),
        Array.getElem_replicate])
    (fun k cw hk _ => absurd hk (by omega))
  rw [hcanon]
  by_cases hmatch : ∃ k cw, FastCodeAt (lengths.toList.map UInt8.toNat) maxBits idx k cw
  · obtain ⟨k, cw, hfca⟩ := hmatch
    rw [spec.2 k cw hfca]
    obtain ⟨hks, _, _⟩ := Huffman.Spec.codeFor_spec hfca.1
    have hmem : (k, cw) ∈ Huffman.Spec.allCodes (lengths.toList.map UInt8.toNat) maxBits :=
      (Huffman.Spec.allCodes_mem_iff _ maxBits k cw).mpr ⟨hks, hfca.1⟩
    rw [treeSlot_match lengths maxBits hmb hv k cw idx hidx hmem hfca.2.1 hfca.2.2]
  · rw [spec.1 hmatch]
    refine (treeSlot_sentinel lengths maxBits hmb hv hbound idx hidx ?_).symm
    rintro ⟨s, cw, hmem, hlen, hcw⟩
    rw [Huffman.Spec.allCodes_mem_iff] at hmem
    exact hmatch ⟨s, cw, hmem.2, hlen, hcw⟩

set_option maxRecDepth 4096 in
/-- **`buildTableCanonical_eq`.** The canonical O(n) decode-table build equals the
    tree-built decode table, under the validity envelope. Drop-in: every decode
    proof transferring through `buildTable` transfers through the canonical build. -/
theorem buildTableCanonical_eq (lengths : Array UInt8) (maxBits : Nat)
    (hmb : maxBits < 32)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (hbound : lengths.size ≤ UInt16.size) :
    HuffTree.buildTableCanonical lengths maxBits
      = HuffTree.buildTable (HuffTree.fromLengthsTree lengths maxBits) := by
  have hsz_canon : (HuffTree.buildTableCanonical lengths maxBits).packed.size = 2 ^ fastBits := by
    show (buildCanonicalLoop _ _ 0 _).size = 2 ^ fastBits
    rw [buildCanonicalLoop_size, Array.size_replicate]
  have hsz_tree : (HuffTree.buildTable (HuffTree.fromLengthsTree lengths maxBits)).packed.size
      = 2 ^ fastBits := by
    show (Array.ofFn _).size = 2 ^ fastBits
    rw [Array.size_ofFn]
  have hpacked : (HuffTree.buildTableCanonical lengths maxBits).packed
      = (HuffTree.buildTable (HuffTree.fromLengthsTree lengths maxBits)).packed := by
    apply Array.ext
    · rw [hsz_canon, hsz_tree]
    · intro i h1 _
      have hi : i < 2 ^ fastBits := by rw [hsz_canon] at h1; exact h1
      rw [← getElem!_pos _ i h1, ← getElem!_pos _ i (by rw [hsz_tree]; exact hi)]
      exact buildTableCanonical_packed_getElem lengths maxBits hmb hv hbound i hi
  exact congrArg HuffTree.DecodeTable.mk hpacked

end Zip.Native.HuffTree
