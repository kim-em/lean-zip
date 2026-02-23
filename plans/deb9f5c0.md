# Review: BitstreamCorrect.lean — proof quality + split write-direction proofs

**Session type**: review (proof quality + file size and organization)

## Current state

- `Zip/Spec/BitstreamCorrect.lean` is **928 lines** — approaching the
  1000-line limit
- BB3 (#29) added ~305 lines of write-direction proofs (bitsToNat,
  writeBitsLSB, bitsToBytes roundtrip) that haven't been reviewed
- 0 sorries in this file
- The file has a clean two-section structure with no cross-dependencies:
  - **Read direction** (lines 1–623, ~620 lines): BitReader ↔ bytesToBits
    correspondence (readBit, readBits, alignToByte, readUInt16LE, readBytes)
  - **Write direction** (lines 624–928, ~305 lines): bitsToNat properties,
    writeBitsLSB roundtrip, bitsToBytes/bytesToBits roundtrip
- The write section only references `Deflate.Spec.*` definitions (from
  Deflate.lean), not any theorems from the read section — the split is clean

## Deliverables

### 1. Review write-direction proofs (lines 624–928) for quality

Focus areas:

**Proof minimization**:
- `bitsToNat_testBit` (line 627): Can the `have htb` + `ext` step be
  combined with `simp`?
- `bitsToNat_bound` (line 646): The `cons` case uses `split <;> omega` —
  can `simp` + `omega` handle the whole case?
- `bitsToBytes_go_eq` (line 777): Uses a `this` wrapper with
  `Nat.strongRecOn` + `subst h`. Is there a simpler pattern?
- `bytesToBits_bitsToBytes_take` (line 882): The elementwise proof is
  ~45 lines with manual index reasoning. Can any of the `by_cases` +
  `getElem_append_left/right` steps be combined?
- Check for sequential `rw` that can be combined

**Slop detection**:
- Are all private helpers used? (`bitsToNat_testBit`,
  `testBit_bitsToNat_ge_length`, `byteToBits_bitsToByte_eq`,
  `bitsToBytes_nil`, `bitsToBytes_cons`, etc.)
- Any duplicated logic between the write-direction helpers and existing
  read-direction helpers?
- Comments that restate what the code does without adding insight

**Lean idioms**:
- Can any `Nat.strongRecOn` inductions use simpler recursion?
- Look for `omega` / `simp` / `grind` opportunities to shorten proofs
- Check if any `private` helpers should be `protected` for cross-file use
  (will be needed when this file is eventually imported by compressor proofs)

### 2. Review read-direction proofs (lines 1–620) for quick wins

Don't do a full deep review (that was partially done before BB3 landed),
but scan for:
- Sequential `rw` that can be combined
- Any dead helpers left over from prior refactors
- `private` visibility on helpers that downstream files might need

### 3. Split file along the read/write boundary

Create `Zip/Spec/BitstreamWriteCorrect.lean` (~305 lines) containing:

**bitsToNat/bitsToByte properties** (lines 624–733):
- `bitsToNat_testBit`, `bitsToNat_bound`, `testBit_bitsToNat`,
  `testBit_bitsToNat_ge`, `testBit_bitsToNat_ge_length`
- `byteToBits_bitsToByte_take8`

**writeBitsLSB properties** (lines 734–761):
- `writeBitsLSB_length`, `readBitsLSB_writeBitsLSB`

**bitsToBytes/bytesToBits roundtrip** (lines 763–928):
- `byteToBits_bitsToByte_eq`, `bitsToBytes_go_eq`, `bitsToBytes_nil`,
  `bitsToBytes_cons`, `byteToBits_bitsToByte_take`, `bytesToBits_data`
- `bytesToBits_bitsToBytes_aligned`, `bytesToBits_bitsToBytes_length_ge`,
  `bytesToBits_bitsToBytes_take`

**Namespace**: Keep `Deflate.Correctness` namespace so all qualified
names remain unchanged.

If the worker determines during review that the split isn't worthwhile
(e.g., the file shrinks below 800 lines after proof minimization, or
there are unexpected cross-dependencies), document the reasoning and
skip the split.

### 4. Update imports and layout

- `Zip.lean` — add `import Zip.Spec.BitstreamWriteCorrect`
- Check if any other file imports BitstreamCorrect and uses write-direction
  theorems (currently unlikely, but verify)
- Update `.claude/CLAUDE.md` source layout table with new file

## Files to create/modify

| File | Action |
|------|--------|
| `Zip/Spec/BitstreamCorrect.lean` | Remove write section, review read section (~620 lines) |
| `Zip/Spec/BitstreamWriteCorrect.lean` | **Create** (~305 lines extracted + reviewed) |
| `Zip.lean` | Add `import Zip.Spec.BitstreamWriteCorrect` |
| `.claude/CLAUDE.md` | Update source layout table |

## Verification

- `lake build` passes
- `lake exe test` passes
- Sorry count unchanged (0 in these files, 4 total in Zip/)
- `BitstreamCorrect.lean` under 700 lines
- `BitstreamWriteCorrect.lean` under 400 lines
- No theorem statements changed (only moved/minimized)
- All qualified names still resolve (namespace preserved)

## Done criteria

- Write-direction proofs reviewed and minimized
- Read-direction scanned for quick wins
- File split completed (or documented decision not to split)
- All imports working, builds clean
- Any proof improvements documented in commit messages
- Source layout table updated
