/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Eval
import Lean.Elab.Deriving.ToExpr
import Std.Data.HashMap

/-! # Integer certificates for the six order-128 auxiliary rows

The generator supplies finite data. Independent checks on bounded integers
verify each row's permutations, strictly ordered keys and multiplicity tags.
The field has order 167772161 and the chosen 128th root is 370529.
-/
set_option autoImplicit false
namespace ProximityGap.AuxiliaryRatioSlotData

abbrev modulus : ℕ := 167772161
abbrev root : ℕ := 370529

/-- The arrays are stored as packed digits. No correctness property depends on
the algorithm which selected a proposed order or tag. -/
structure Archive where
  heavyCount : ℕ
  tripleKey : ℕ
  ratios : ℕ
  keys : ℕ
  pairTags : ℕ
  pairKeys : ℕ
  pairOrder : ℕ
  pairRanks : ℕ
  chargeTags : ℕ
  chargeOrder : ℕ
  chargeRanks : ℕ
  deriving Lean.ToExpr, Inhabited

/-- Read a digit without constructing the list of preceding entries. -/
def digit (a width index : ℕ) := (a >>> (width*index)) % (2^width)

private def pack (w : ℕ) (xs : Array ℕ) : ℕ :=
  xs.foldr (fun x a => x + (a <<< w)) 0

private def ranks (n : ℕ) (ids : Array ℕ) : Array ℕ := Id.run do
  let mut v := Array.replicate n 0
  for j in [:ids.size] do v := v.set! ids[j]! j
  return v

private def propose (d : ℕ) : Archive := Id.run do
  let v := root.powMod d modulus
  let rs := (Array.range 128).map fun i =>
    let x := root.powMod i modulus
    ((modulus+1-x) * (modulus+v-x).powMod (modulus-2) modulus) % modulus
  let mut freq : Std.HashMap ℕ ℕ := ∅
  let mut pairs := #[]
  let mut pTags := Array.replicate (128*128) 0
  for i in [1:128] do
    for j in [i+1:128] do
      if i != d && j != d then
        let T := rs[i]! * rs[j]! % modulus
        let tag := freq.getD T 0
        freq := freq.insert T (tag+1)
        let id := 128*i+j
        pTags := pTags.set! id tag
        pairs := pairs.push (T*128+tag,id)
  let keys := ((freq.toArray.filter fun c => c.2>1).map Prod.fst).qsort (· < ·)
  let big := keys.findIdx (fun T => freq.getD T 0 > 2)
  let keyOf := (Array.range keys.size).foldl (fun (m : Std.HashMap ℕ ℕ) i => m.insert keys[i]! i) ∅
  let pIdx := (Array.range (128*128)).map fun id =>
    keyOf.getD ((rs[id/128]! * rs[id%128]!) % modulus) 0
  let pairOrder := (pairs.qsort (fun a b => a.1 < b.1)).map Prod.snd
  let mut marks : Std.HashMap ℕ ℕ := ∅
  let mut charges := #[]
  let mut cTags := Array.replicate ((keys.size+2)*128) 0
  for layer in [:keys.size+2] do
    let T := keys[if layer<keys.size then layer else big]!
    for x in [1:128] do
      if x != d then
        let z := T*rs[x]!%modulus
        let t := marks.getD z 0
        marks := marks.insert z (t+1)
        let id := 128*layer+x
        cTags := cTags.set! id t
        charges := charges.push (z*16+t,id)
  let chargeOrder := (charges.qsort (fun a b => a.1 < b.1)).map Prod.snd
  return ⟨keys.size,big,pack 28 rs,pack 28 keys,pack 6 pTags,pack 8 pIdx,pack 14 pairOrder,
    pack 13 (ranks (128*128) pairOrder),pack 4 cTags,pack 15 chargeOrder,
    pack 15 (ranks ((keys.size+2)*128) chargeOrder)⟩

set_option maxRecDepth 50000 in
private def a1 : Archive := eval% propose 1
private def a2 : Archive := eval% propose 2
private def a4 : Archive := eval% propose 4
private def a8 : Archive := eval% propose 8
private def a16 : Archive := eval% propose 16
private def a32 : Archive := eval% propose 32

/-- Only six separations are needed after conjugating the primitive root. -/
def data (d : ℕ) : Archive := match d with
  | 1 => a1 | 2 => a2 | 4 => a4 | 8 => a8 | 16 => a16 | _ => a32

def validSite (d i : ℕ) : Bool := 0<i && i<128 && i != d
def validPair (d id : ℕ) : Bool := validSite d (id/128) && validSite d (id%128) && id/128<id%128

def pairValue (a : Archive) (id : ℕ) :=
  digit a.ratios 28 (id/128) * digit a.ratios 28 (id%128) % modulus

def pairCode (a : Archive) (id : ℕ) := pairValue a id * 128 + digit a.pairTags 6 id

def chargeValue (a : Archive) (id : ℕ) :=
  let h := id/128
  digit a.keys 28 (if h<a.heavyCount then h else a.tripleKey) * digit a.ratios 28 (id%128) % modulus

def chargeCode (a : Archive) (id : ℕ) := chargeValue a id * 16 + digit a.chargeTags 4 id

/-- A valid pair has a unique ordered position. Positive tags must belong to
a named heavy key and tags at least two belong to the triple-charge key. -/
def checkPair (a : Archive) (d id : ℕ) : Bool :=
  !validPair d id || (
    let r := digit a.pairRanks 13 id
    let t := digit a.pairTags 6 id
    let h := digit a.pairKeys 8 id
    r<7875 && digit a.pairOrder 14 r == id &&
      (t==0 || (h<a.heavyCount && digit a.keys 28 h == pairValue a id && (t==1 || h==a.tripleKey))))

def checkPairOrder (a : Archive) (j : ℕ) : Bool :=
  pairCode a (digit a.pairOrder 14 j) < pairCode a (digit a.pairOrder 14 (j+1))

/-- The repeated heavy keys are three layers for the distinguished key and
one for each other key. Each scale has at most twelve ordered slots. -/
def checkCharge (a : Archive) (d id : ℕ) : Bool :=
  !validSite d (id%128) || (
    let r := digit a.chargeRanks 15 id
    r<(a.heavyCount+2)*126 && digit a.chargeOrder 15 r == id && digit a.chargeTags 4 id < 12)

def checkChargeOrder (a : Archive) (j : ℕ) : Bool :=
  chargeCode a (digit a.chargeOrder 15 j) < chargeCode a (digit a.chargeOrder 15 (j+1))

end ProximityGap.AuxiliaryRatioSlotData
