import Zip.Spec.Deflate

/-!
# Well-Founded Recursion Prototype for DEFLATE CL Symbol Decoding

This file prototypes replacing fuel-based recursion with well-founded
recursion for `decodeDynamicTables.decodeCLSymbols`. The decreasing
measure is `totalCodes - acc.length`: the accumulator grows by at
least 1 on every recursive call and is bounded above by `totalCodes`.

This is a Track C2 prototype — validating the approach before
converting the remaining fuel-based functions.

## Key Takeaways

1. **Termination proof works**: `termination_by totalCodes - acc.length`
   with `decreasing_by` using `simp_all` + `omega` handles all branches
   automatically.

2. **Structural change needed**: The fuel-based version uses `do` notation
   with `guard`. The WF version must use explicit `if/match` so that the
   termination checker can extract guard conditions as hypotheses. This is
   a mechanical but pervasive change.

3. **Equivalence proof considerations**: Proving the WF version equals the
   fuel version requires aligning `do`-notation (Option monad bind chains
   with `guard`) against explicit `match/if`. The main friction points are:
   - `guard (acc.length > 0)` vs `if acc.length == 0 then none`
     (BEq vs Prop, negation flip)
   - Monadic `←` vs explicit `match` on `Option` results
   - `let ... := ...` in `do` blocks introducing `have` vs `let`

   When converting in-place, both sides share the same structure, making
   this issue disappear. Alternatively, the fuel-independence theorems
   already establish that the fuel version stabilizes — proving the WF
   version equals the stable value is the only needed theorem.

4. **Conversion strategy**: When converting in-place, rewrite the function
   to remove the fuel parameter and add `termination_by`. All proofs that
   `unfold` the function will need updating to match the new (non-monadic)
   structure. The fuel-independence theorems become trivial or can be
   removed entirely.
-/

namespace Deflate.Spec

/-- Well-founded version of `decodeDynamicTables.decodeCLSymbols`.
    Uses `termination_by totalCodes - acc.length` instead of fuel.
    Behaviorally equivalent to the fuel-based version when sufficient
    fuel is provided. -/
def decodeCLSymbolsWF (clTable : List (Huffman.Spec.Codeword × Nat))
    (totalCodes : Nat) (acc : List Nat) (bits : List Bool) :
    Option (List Nat × List Bool) :=
  if acc.length ≥ totalCodes then some (acc, bits)
  else
    match Huffman.Spec.decode clTable bits with
    | none => none
    | some (sym, bits) =>
      if sym < 16 then
        decodeCLSymbolsWF clTable totalCodes (acc ++ [sym]) bits
      else if sym == 16 then
        if acc.length == 0 then none
        else
          match readBitsLSB 2 bits with
          | none => none
          | some (rep, bits) =>
            let acc' := acc ++ List.replicate (rep + 3) acc.getLast!
            if acc'.length ≤ totalCodes then
              decodeCLSymbolsWF clTable totalCodes acc' bits
            else none
      else if sym == 17 then
        match readBitsLSB 3 bits with
        | none => none
        | some (rep, bits) =>
          let acc' := acc ++ List.replicate (rep + 3) 0
          if acc'.length ≤ totalCodes then
            decodeCLSymbolsWF clTable totalCodes acc' bits
          else none
      else if sym == 18 then
        match readBitsLSB 7 bits with
        | none => none
        | some (rep, bits) =>
          let acc' := acc ++ List.replicate (rep + 11) 0
          if acc'.length ≤ totalCodes then
            decodeCLSymbolsWF clTable totalCodes acc' bits
          else none
      else none
termination_by totalCodes - acc.length
decreasing_by all_goals simp_all [List.length_append, List.length_replicate]; omega

end Deflate.Spec
