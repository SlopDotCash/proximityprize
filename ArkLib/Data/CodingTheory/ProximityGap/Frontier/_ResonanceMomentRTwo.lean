/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPhaseResonance

/-!
# The `r = 2` rung of the resonance moment (#407 / #444)

Extends `GaussPhaseResonance` (the named `sqrt p`-free free variable of the prize) and the
`r = 1` base case in `_ResonanceMomentBaseCase`. The base file pins `phaseSum u 1 c` and
`T 1 = m - 1` (the trivial Parseval rung). This file supplies the NEXT rung `r = 2`, which
is the first genuinely non-diagonal phase-sum: a convolution of the unit phases.

## The convolution collapse

> `phaseSum u 2 c = sum_{a != 0, c - a != 0} u(a) * u(c - a)`.

The depth-2 phase-sum is the restricted autocorrelation/convolution of the phase vector at `c`,
ranging over the off-diagonal pairs `(a, c - a)` with both coordinates nonzero. This is the
exact `r = 2` analogue of the base file's `phaseSum_one` collapse, grep-confirmed missing.

## The `c = 0` diagonal value for conjugate-symmetric unit phases

The Gauss-sum unit phases satisfy `u(-a) = conj(u(a))` (up to the `chi(-1)` twist; the honest
structural sub-case is the real-symmetric one `u(-a) = conj(u(a))`). Under that hypothesis the
`c = 0` phase-sum collapses to the diagonal L2-mass:

> `phaseSum u 2 0 = sum_{a != 0} u(a) * u(-a) = sum_{a != 0} ‖u(a)‖^2 = m - 1`  (REAL).

Hence the resonance moment at `r = 2` is bounded BELOW by the squared diagonal mass:

> `T 2 = resonanceMoment u 2 >= ‖phaseSum u 2 0‖^2 = (m - 1)^2`.

This is a genuine LOWER bound on the `r = 2` rung. The off-diagonal (`c != 0`) terms only add
to it, strictly above the trivial `T 2 >= 0`.

## Honest scope

This is the `r = 2` rung, the SECOND rung, still FAR below the binding depth `r ~ log m` where
the `ResonanceConjecture` is the recognized open Gauss-period / BGK content. The lower bound
`(m-1)^2 <= (2 m log m)^2` is consistent with the conjecture, not a proof of it. NO capacity /
beyond-Johnson / sub-linear / closure claim; CORE `M(mu_n) <= C sqrt(n log m)` UNCHANGED / OPEN.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issues #407, #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators Classical
open Finset

variable {m : ℕ} [NeZero m]

/-- The `r = 2` filter membership criterion: a pair `X : Fin 2 -> ZMod m` lies in the
phase-sum filter at `c` iff `X 0 != 0`, `X 1 != 0`, and `X 0 + X 1 = c`. -/
theorem mem_phaseSum_two_filter (c : ZMod m) (X : Fin 2 → ZMod m) :
    (X ∈ (Finset.univ.filter (fun X : Fin 2 → ZMod m =>
        (∀ i, X i ≠ 0) ∧ (∑ i, X i) = c))) ↔
      (X 0 ≠ 0 ∧ X 1 ≠ 0 ∧ X 0 + X 1 = c) := by
  classical
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, hsum⟩
    refine ⟨hne 0, hne 1, ?_⟩
    simpa [Fin.sum_univ_two] using hsum
  · rintro ⟨h0, h1, hsum⟩
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i
      · exact h0
      · exact h1
    · simpa [Fin.sum_univ_two] using hsum

/-- **`phaseSum u 2 c = sum_{a != 0, c - a != 0} u(a) * u(c - a)`.** The depth-2 phase-sum is the
off-diagonal restricted convolution of the unit phases at `c`. -/
theorem phaseSum_two (u : ZMod m → ℂ) (c : ZMod m) :
    phaseSum u 2 c =
      ∑ a ∈ Finset.univ.filter (fun a : ZMod m => a ≠ 0 ∧ c - a ≠ 0),
        u a * u (c - a) := by
  classical
  unfold phaseSum
  -- reindex the Fin 2 -> ZMod m filter by its first coordinate `X 0`
  refine Finset.sum_nbij' (fun X => X 0) (fun a => ![a, c - a]) ?_ ?_ ?_ ?_ ?_
  · -- maps into the target filter
    intro X hX
    rw [mem_phaseSum_two_filter] at hX
    obtain ⟨h0, h1, hsum⟩ := hX
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, h0, ?_⟩
    have : c - X 0 = X 1 := by rw [← hsum]; ring
    rw [this]; exact h1
  · -- inverse maps back into the source filter
    intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨_, h0, h1⟩ := ha
    rw [mem_phaseSum_two_filter]
    refine ⟨by simpa using h0, by simpa using h1, ?_⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  · -- left inverse
    intro X hX
    rw [mem_phaseSum_two_filter] at hX
    obtain ⟨_, _, hsum⟩ := hX
    funext i
    fin_cases i
    · simp
    · simp only [Matrix.cons_val_one]
      have hgoal : c - X 0 = X 1 := by
        rw [sub_eq_iff_eq_add, add_comm]; exact hsum.symm
      exact hgoal
  · -- right inverse
    intro a _
    simp
  · -- the summand matches
    intro X hX
    rw [mem_phaseSum_two_filter] at hX
    obtain ⟨_, _, hsum⟩ := hX
    have : X 1 = c - X 0 := by rw [← hsum]; ring
    rw [Fin.prod_univ_two, this]

/-- For a conjugate-symmetric unit-phase vector (`u(-a) = conj(u a)` and `‖u a‖ = 1`), the
`c = 0` depth-2 phase-sum collapses to the diagonal L2-mass:
`phaseSum u 2 0 = sum_{a != 0} ‖u a‖^2 = m - 1` (as a complex number, real and equal to `m-1`). -/
theorem phaseSum_two_zero_of_conjSymm (u : ZMod m → ℂ)
    (hu : ∀ l : ZMod m, ‖u l‖ = 1) (hsymm : ∀ a : ZMod m, u (-a) = (starRingEnd ℂ) (u a)) :
    phaseSum u 2 0 = ((m : ℝ) - 1 : ℝ) := by
  classical
  rw [phaseSum_two]
  -- at c = 0, the filter is {a : a != 0} (since 0 - a != 0 iff a != 0)
  have hfilt : (Finset.univ.filter (fun a : ZMod m => a ≠ 0 ∧ (0 : ZMod m) - a ≠ 0)) =
      Finset.univ.filter (fun a : ZMod m => a ≠ 0) := by
    apply Finset.filter_congr
    intro a _
    constructor
    · rintro ⟨h, _⟩; exact h
    · intro h
      refine ⟨h, ?_⟩
      simpa using fun hc => h (by simpa using hc)
  rw [hfilt]
  -- each term u a * u (0 - a) = u a * u (-a) = u a * conj (u a) = ‖u a‖^2 = 1
  have hterm : ∀ a ∈ Finset.univ.filter (fun a : ZMod m => a ≠ 0),
      u a * u ((0 : ZMod m) - a) = (1 : ℂ) := by
    intro a _
    have h0a : (0 : ZMod m) - a = -a := by ring
    rw [h0a, hsymm a, Complex.mul_conj]
    have hns : Complex.normSq (u a) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hu a]; norm_num
    rw [hns]; norm_num
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (Finset.univ.filter (fun a : ZMod m => a ≠ 0)).card = m - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0),
      Finset.card_univ, ZMod.card]
  rw [hcard]
  have hm : 1 ≤ m := NeZero.one_le
  push_cast [Nat.cast_sub hm]
  norm_num

/-- **`T 2 >= (m - 1)^2`** for a conjugate-symmetric unit-phase vector. The resonance moment at
`r = 2` is bounded below by the squared diagonal mass `‖phaseSum u 2 0‖^2 = (m-1)^2`: the
off-diagonal residues only add to it. A genuine `r = 2` lower bound above the trivial `T 2 >= 0`. -/
theorem resonanceMoment_two_ge_of_conjSymm (u : ZMod m → ℂ)
    (hu : ∀ l : ZMod m, ‖u l‖ = 1) (hsymm : ∀ a : ZMod m, u (-a) = (starRingEnd ℂ) (u a)) :
    (((m : ℝ) - 1) ^ 2 : ℝ) ≤ resonanceMoment u 2 := by
  classical
  unfold resonanceMoment
  have hmem : (0 : ZMod m) ∈ (Finset.univ : Finset (ZMod m)) := Finset.mem_univ 0
  have hsingle : ‖phaseSum u 2 0‖ ^ 2 ≤
      ∑ c : ZMod m, ‖phaseSum u 2 c‖ ^ 2 := by
    apply Finset.single_le_sum (f := fun c => ‖phaseSum u 2 c‖ ^ 2)
      (fun c _ => by positivity) hmem
  have hval : ‖phaseSum u 2 0‖ ^ 2 = ((m : ℝ) - 1) ^ 2 := by
    rw [phaseSum_two_zero_of_conjSymm u hu hsymm]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [← hval]; exact hsingle

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.phaseSum_two
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.phaseSum_two_zero_of_conjSymm
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_two_ge_of_conjSymm
