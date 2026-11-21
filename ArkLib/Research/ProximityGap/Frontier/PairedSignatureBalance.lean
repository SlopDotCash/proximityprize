/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuotientSignatureCensus

/-! # A subtree test for simultaneous locator signatures

Negating the quotient roots exchanges sibling occupancies. On a complete subtree
each strict descendant contributes with the same total multiplicity before and
after negation. Only the two inherited path sums can change the difference.
-/

namespace ProximityGap.PairedSignatureBalance

open QuotientSignatureCensus

/-- A complete tree with both locator signatures prescribed on every leaf. -/
inductive Complete : ℕ → Tree → Prop
  | leaf (v w : ℕ) : Complete 0 (.leaf v (some w))
  | fork {n : ℕ} {l r : Tree} :
      Complete n l → Complete n r → Complete (n + 1) (.fork l r)

/-- Sum of the original signature over the leaves of a subtree. -/
def original : Tree → ℕ
  | .leaf v _ => v
  | .fork l r => original l + original r

/-- Sum of the required opposite signature over the leaves of a subtree. -/
def opposite : Tree → ℕ
  | .leaf _ w => w.getD 0
  | .fork l r => opposite l + opposite r

/-- The difference in required signature sums is the leaf count times the difference in offsets. -/
theorem sums_eq {n : ℕ} {t : Tree} (ht : Complete n t) (x y : ℕ) (c : Tail t)
    (hc : accepted t x y c = true) :
    original t + 2 ^ n * y = opposite t + 2 ^ n * x := by
  induction ht generalizing x y with
  | leaf v w =>
    obtain ⟨rfl, rfl⟩ : x = v ∧ w = y := by simpa [accepted] using hc
    simp [original, opposite]
    omega
  | fork hl hr il ir =>
    obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp hc
    have hL := il _ _ _ h₁
    have hR := ir _ _ _ h₂
    simp only [original, opposite, pow_succ]
    simp only [Nat.mul_add] at hL hR
    ring_nf at hL hR ⊢
    omega

/-- Unequal residues exclude an entire pair of subtrees before counting any root sets. -/
theorem residue_eq {n : ℕ} {t : Tree} (ht : Complete n t) (x y : ℕ) (c : Tail t)
    (hc : accepted t x y c = true) : original t ≡ opposite t [MOD 2 ^ n] := by
  have h := congrArg (· % (2 ^ n)) (sums_eq ht x y c hc)
  simpa [Nat.ModEq] using h

/-- At the root the two offsets agree, so the two complete leaf sums agree exactly. -/
theorem root_eq {n : ℕ} {t : Tree} (ht : Complete n t) (c : Choice × Tail t)
    (hc : fullAccepted t c = true) : original t = opposite t :=
  Nat.add_right_cancel (sums_eq ht _ _ _ hc)

/-- Incompatible subtree residues contribute zero to the verified weighted census. -/
theorem mass_zero_of_residue_ne {n : ℕ} {t : Tree} (ht : Complete n t) (B x y : ℕ)
    (hne : ¬ original t ≡ opposite t [MOD 2 ^ n]) : mass B t x y = 0 := by
  rw [mass_eq_sum]
  apply Finset.sum_eq_zero
  intro c _
  exact ite_eq_right fun h => hne (residue_eq ht x y c h)

#print axioms mass_zero_of_residue_ne
#print axioms sums_eq
#print axioms residue_eq
#print axioms root_eq

end ProximityGap.PairedSignatureBalance
