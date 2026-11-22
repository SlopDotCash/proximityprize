/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.AuxiliaryRatioSlotData
import Mathlib.Tactic

/-! # Kernel checks of six tables of cross-ratio products

Each sorted table is checked in blocks. Splitting the declarations keeps the
kernel's memory use bounded. The tables are proof inputs only.
-/
set_option autoImplicit false
namespace ProximityGap.AuxiliaryRatioSlotData

/-- Check a contiguous integer interval. -/
def interval (f : ℕ → Bool) (lo : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => f (lo+n) && interval f lo n

theorem interval_iff (f : ℕ → Bool) (lo n : ℕ) :
    interval f lo n=true ↔ ∀ i, lo ≤ i → i<lo+n → f i=true := by
  induction n with
  | zero =>
    simp only [interval, true_iff, Nat.add_zero]
    omega
  | succ n ih =>
    rw [interval,Bool.and_eq_true,ih]
    constructor
    · rintro ⟨last,rest⟩ i lb ub
      by_cases edge : i=lo+n
      · rwa [edge]
      · exact rest i lb (by omega)
    · intro h
      exact ⟨h _ (by omega) (by omega),fun i lb ub => h i lb (by omega)⟩

private def validRange (f : ℕ → Bool) (lo hi : ℕ) : Prop :=
  ∀ i, lo ≤ i → i < hi → f i = true

private theorem joinRanges (f : ℕ → Bool) (lo mid hi : ℕ)
    (a : validRange f lo mid) (b : validRange f mid hi) : validRange f lo hi := by
  intro i h₁ h₂
  by_cases left : i < mid
  · exact a i h₁ left
  · exact b i (by omega) h₂

/-- For ratios, multiplication verifies the proposed value without modular
division inside the certificate. The remaining clauses check the order of
the heavy keys and the two rank tables. -/
def checkAt (d i : ℕ) : Bool :=
  let a := data d
  let x := Nat.powMod root i modulus
  let v := Nat.powMod root d modulus
  (i≥128 || !validSite d i || (
    digit a.ratios 28 i < modulus &&
    (digit a.ratios 28 i * (modulus+v-x)) % modulus == (modulus+1-x)%modulus)) &&
  (i≥a.heavyCount || digit a.keys 28 i < modulus) &&
  (i+1≥a.heavyCount || digit a.keys 28 i < digit a.keys 28 (i+1)) &&
  (i≥16384 || checkPair a d i) &&
  (i+1≥7875 || checkPairOrder a i) &&
  (i≥(a.heavyCount+2)*128 || checkCharge a d i) &&
  (i+1≥(a.heavyCount+2)*126 || checkChargeOrder a i)

open Lean Elab Command in
/-- Split a fixed row into 48 independently kernel-reduced blocks. -/
elab "certify_ratio_row " d:num " as " name:ident : command => do
  let mut parts : Array (Nat × Nat × TSyntax `term) := #[]
  for j in [:48] do
    let id := mkIdent (name.getId.appendAfter ("_block" ++ toString j))
    let lo := Syntax.mkNumLit (toString (512*j))
    let hi := Syntax.mkNumLit (toString (512*j+512))
    elabCommand (← `(private theorem $id : validRange (checkAt $d) $lo $hi :=
      (interval_iff (checkAt $d) $lo 512).mp (by decide +kernel)))
    parts := parts.push (512*j, 512, ← `($id:ident))
  while parts.size > 1 do
    let mut next : Array (Nat × Nat × TSyntax `term) := #[]
    for j in [:(parts.size+1)/2] do
      let left := parts[2*j]!
      if 2*j+1 < parts.size then
        let right := parts[2*j+1]!
        let lo := Syntax.mkNumLit (toString left.1)
        let mid := Syntax.mkNumLit (toString right.1)
        let hi := Syntax.mkNumLit (toString (right.1+right.2.1))
        let joined ← `(joinRanges (checkAt $d) $lo $mid $hi $(left.2.2) $(right.2.2))
        next := next.push (left.1,left.2.1 + right.2.1,joined)
      else next := next.push left
    parts := next
  let result := parts[0]!.2.2
  elabCommand (← `(private theorem $name : validRange (checkAt $d) 0 24576 := $result))

set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

certify_ratio_row 1 as row1
certify_ratio_row 2 as row2
certify_ratio_row 4 as row4
certify_ratio_row 8 as row8
certify_ratio_row 16 as row16
certify_ratio_row 32 as row32

theorem checked {d i : ℕ} (row : d=1 ∨ d=2 ∨ d=4 ∨ d=8 ∨ d=16 ∨ d=32)
    (inside : i<24576) : checkAt d i=true := by
  have all : validRange (checkAt d) 0 24576 := by
    rcases row with rfl|rfl|rfl|rfl|rfl|rfl
    · exact row1
    · exact row2
    · exact row4
    · exact row8
    · exact row16
    · exact row32
  exact all i (Nat.zero_le _) inside

end ProximityGap.AuxiliaryRatioSlotData
#print axioms ProximityGap.AuxiliaryRatioSlotData.checked
