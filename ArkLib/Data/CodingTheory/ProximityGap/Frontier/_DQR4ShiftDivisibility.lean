/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DQR4CrossMomentRepLocalization
import Mathlib.GroupTheory.PGroup

/-!
# DQR-4 integrality: the zero-sum count is divisible by every prime depth — #466

Tenth result of the DQR arc; formalizes the probe-verified shift divisibility
(`probe_dqr4_zero_rep_divisibility.py`). The cyclic group `ℤ/r` acts on the zero-sum solution
set `{y ∈ G^r : ∑ y = 0}` by index rotation; for prime `r` with `(r : F) ≠ 0` and `0 ∉ G` the
action has NO fixed points (a fixed tuple is constant, forcing `r·y₀ = 0`, hence `y₀ = 0`),
so the p-group fixed-point congruence gives

* `shift_dvd_repCount_zero` :  `r ∣ f_r(0)`  (`r` prime, `(r : F) ≠ 0`, `0 ∉ G`).

Through `oddPowerSum_eq_rep_zero` this is an exact integrality constraint on the odd power
sums of the Paley spectrum (`P_r = q·f_r(0) − n^r`), hence on the twist-average closed form
`P_k·P_j` of the signed ledger. The companion dilation divisibility (`n ∣` statements, free
`G`-action) is the recorded next brick. Issue #466. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset MulAction
open ArkLib.ProximityGap.Frontier.DQR4CrossMomentRepLocalization

namespace ArkLib.ProximityGap.Frontier.DQR4ShiftDivisibility

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The zero-sum solutions with `ℤ/r`-indexed coordinates (rotation-friendly form). -/
noncomputable def zmodSolutions (G : Finset F) (r : ℕ) [NeZero r] : Finset (ZMod r → F) :=
  (Fintype.piFinset (fun _ : ZMod r => G)).filter (fun y => ∑ i, y i = 0)

/-- Reindexing along `Fin r ≃ ZMod r`: the rotation-friendly count IS `f_r(0)`. -/
theorem zmodSolutions_card (G : Finset F) (r : ℕ) [NeZero r] :
    (zmodSolutions G r).card = repCount G r (0 : F) := by
  classical
  have e : Fin r ≃ ZMod r := (ZMod.finEquiv r).toEquiv
  unfold zmodSolutions repCount
  apply Finset.card_nbij' (i := fun y => y ∘ e) (j := fun y => y ∘ e.symm)
  · intro y hy
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Fintype.mem_piFinset] at hy ⊢
    refine ⟨fun i => hy.1 (e i), ?_⟩
    rw [← hy.2]
    exact Fintype.sum_equiv e _ _ (fun i => rfl)
  · intro y hy
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Fintype.mem_piFinset] at hy ⊢
    refine ⟨fun i => hy.1 (e.symm i), ?_⟩
    rw [← hy.2]
    exact Fintype.sum_equiv e.symm _ _ (fun i => rfl)
  · intro y _
    funext i
    simp
  · intro y _
    funext i
    simp

/-- The rotation action of `Multiplicative (ZMod r)` on the zero-sum solutions. -/
noncomputable instance rotAction (G : Finset F) (r : ℕ) [NeZero r] :
    MulAction (Multiplicative (ZMod r)) {y // y ∈ zmodSolutions G r} where
  smul s y := ⟨fun i => y.1 (i + s.toAdd), by
    have hy := y.2
    simp only [zmodSolutions, Finset.mem_filter, Fintype.mem_piFinset] at hy ⊢
    refine ⟨fun i => hy.1 (i + s.toAdd), ?_⟩
    exact (Fintype.sum_equiv (Equiv.addRight s.toAdd)
      (fun i => y.1 (i + s.toAdd)) y.1 (fun i => rfl)).trans hy.2⟩
  one_smul y := by
    apply Subtype.ext
    funext i
    show y.1 (i + (1 : Multiplicative (ZMod r)).toAdd) = y.1 i
    rw [toAdd_one, add_zero]
  mul_smul s t y := by
    apply Subtype.ext
    funext i
    show y.1 (i + (s * t).toAdd) = y.1 (i + s.toAdd + t.toAdd)
    rw [toAdd_mul, ← add_assoc]

/-- **Shift divisibility**: for prime `r` with `(r : F) ≠ 0` and `0 ∉ G`,
`r ∣ f_r(0)` — the rotation action is fixed-point-free, so the p-group congruence forces the
zero-sum count into the ideal `(r)`. -/
theorem shift_dvd_repCount_zero (G : Finset F) {r : ℕ} (hr : r.Prime)
    (hrF : (r : F) ≠ 0) (h0 : (0 : F) ∉ G) :
    r ∣ repCount G r (0 : F) := by
  haveI : NeZero r := ⟨hr.ne_zero⟩
  haveI : Fact r.Prime := ⟨hr⟩
  -- the acting group is an r-group.
  have hpg : IsPGroup r (Multiplicative (ZMod r)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_eq_fintype_card]; simp [ZMod.card])
  -- no fixed points: a rotation-invariant tuple is constant with `r·y₀ = 0`.
  have hfix : IsEmpty (fixedPoints (Multiplicative (ZMod r))
      {y // y ∈ zmodSolutions G r}) := by
    refine ⟨fun z => ?_⟩
    obtain ⟨y, hy⟩ := z
    -- constancy: `y (0 + s) = y 0` for every shift `s`.
    have hconst : ∀ i : ZMod r, y.1 i = y.1 0 := by
      intro i
      have h := congrArg (fun z : {y // y ∈ zmodSolutions G r} => z.1 (0 : ZMod r))
        (hy (Multiplicative.ofAdd i))
      calc y.1 i = y.1 (0 + i) := by rw [zero_add]
        _ = y.1 0 := h
    -- the sum is `r · y₀ = 0`, so `y₀ = 0`, contradicting `0 ∉ G`.
    have hy2 := y.2
    simp only [zmodSolutions, Finset.mem_filter, Fintype.mem_piFinset] at hy2
    have hsum : ∑ i : ZMod r, y.1 i = (r : F) * y.1 0 := by
      rw [Finset.sum_congr rfl (fun i _ => hconst i), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      congr 1
      simp [ZMod.card]
    have hmul : (r : F) * y.1 0 = 0 := hsum.symm.trans hy2.2
    rcases mul_eq_zero.mp hmul with h | h
    · exact hrF h
    · exact h0 (h ▸ hy2.1 0)
  -- the congruence: card ≡ 0 mod r.
  have hcong := hpg.card_modEq_card_fixedPoints {y // y ∈ zmodSolutions G r}
  have hfz : Nat.card (fixedPoints (Multiplicative (ZMod r))
      {y // y ∈ zmodSolutions G r}) = 0 := Nat.card_of_isEmpty
  rw [hfz] at hcong
  have hdvd : r ∣ Nat.card {y // y ∈ zmodSolutions G r} :=
    (Nat.modEq_zero_iff_dvd).mp hcong
  rwa [Nat.card_eq_fintype_card, Fintype.card_coe, zmodSolutions_card] at hdvd

end ArkLib.ProximityGap.Frontier.DQR4ShiftDivisibility

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.DQR4ShiftDivisibility.zmodSolutions_card
#print axioms ArkLib.ProximityGap.Frontier.DQR4ShiftDivisibility.shift_dvd_repCount_zero
