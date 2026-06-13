import Zip.Native.Inflate

namespace Scratch2
open Zip.Native

def findTableCode.go (baseTable : Array UInt16) (extraTable : Array UInt8)
    (value : Nat) (i : Nat) (hsize : baseTable.size ≤ extraTable.size) :
    Option (Nat × Nat × UInt32) :=
  if h1 : i + 1 < baseTable.size then
    if baseTable[i + 1].toNat > value then
      let extra := (extraTable[i]'(by omega)).toNat
      let extraVal := (value - (baseTable[i]'(by omega)).toNat).toUInt32
      some (i, extra, extraVal)
    else
      findTableCode.go baseTable extraTable value (i + 1) hsize
  else if h2 : i < baseTable.size then
    let extra := (extraTable[i]'(by omega)).toNat
    let extraVal := (value - baseTable[i].toNat).toUInt32
    some (i, extra, extraVal)
  else
    none
termination_by baseTable.size - i

def findTableCode (baseTable : Array UInt16) (extraTable : Array UInt8)
    (value : Nat) (hsize : baseTable.size ≤ extraTable.size := by decide) :
    Option (Nat × Nat × UInt32) :=
  findTableCode.go baseTable extraTable value 0 hsize

def findDistCode (dist : Nat) : Option (Nat × Nat × UInt32) :=
  findTableCode Inflate.distBase Inflate.distExtra dist

@[inline] private def packCode (idx extraN : Nat) (extraV : UInt32) : UInt32 :=
  idx.toUInt32 ||| (extraN.toUInt32 <<< 8) ||| (extraV <<< 16)

-- V1: map-over-range (inherited shape)
def distCodeTab : Array UInt32 :=
  (Array.range 32769).map fun dist =>
    match findDistCode dist with
    | some (idx, en, ev) => packCode idx en ev
    | none => 0

@[simp] theorem distCodeTab_size : distCodeTab.size = 32769 := by
  simp [distCodeTab]

private theorem getElem_map_range {n : Nat} {f : Nat → UInt32} {i : Nat}
    (hi : i < ((Array.range n).map f).size) :
    ((Array.range n).map f)[i] = f i := by
  rw [Array.getElem_map, Array.getElem_range]

private theorem distCodeTab_getElem {dist idx en : Nat} {ev : UInt32} (hdist : dist < 32769)
    (h : findDistCode dist = some (idx, en, ev)) :
    distCodeTab[dist]'(distCodeTab_size ▸ hdist) = packCode idx en ev := by
  have := getElem_map_range (n := 32769)
    (f := fun dist => match findDistCode dist with
      | some (idx, en, ev) => packCode idx en ev
      | none => 0)
    (i := dist) (by simp [hdist])
  rw [show distCodeTab[dist]'(distCodeTab_size ▸ hdist)
      = ((Array.range 32769).map (fun dist => match findDistCode dist with
          | some (idx, en, ev) => packCode idx en ev
          | none => 0))[dist]'(by simp [hdist]) from rfl, this, h]

end Scratch2
