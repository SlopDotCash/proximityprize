/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPhaseResonance

/-!
# Diagonal extraction of the resonance moment — isolating the Wick floor (door-(iv), Lane 2/3)

The resonance moment `T r = ∑_c ‖phaseSum u r c‖²` is the `√p`-free open core of the prize.  Expanding the
squared norm of each phase-sum as a double sum over its fiber and regrouping by the *agreement relation*
`∑ X = ∑ Y`, the resonance moment is exactly a paired double sum

> `T r = ∑_{(X,Y) : (∀i X i≠0) ∧ (∀i Y i≠0) ∧ ∑X=∑Y}  conj(∏ u(X)) · (∏ u(Y))   (as a complex number,`
> `       and its real part is `T r`).`

The **diagonal** `X = Y` contributes `∑_X ‖∏ u(X i)‖²`, which for unit-modulus phases (`‖u a‖ = 1`) is the
clean count `(m-1)^r` — the **Wick floor** of the resonance moment.  This file makes that decomposition
explicit and pins the diagonal value, isolating the *off-diagonal agreement term* (`X ≠ Y`, `∑X=∑Y`) as
the single open object: the entire `√`-cancellation question is whether this off-diagonal stays bounded.

This complements the phase-mass arc (`_ResonancePhaseMassFloor`, `_ResonancePhaseMassExtremizer`): the
phase mass `|S|` controls the *coherent* part, while the diagonal extraction names the *Wick* part and the
agreement off-diagonal that the prize must control.  No CORE / cancellation / completion / moment /
anti-concentration / capacity claim (the off-diagonal is NAMED, not bounded).  Self-contained leaf over
`GaussPhaseResonance`.  Axiom-clean (`{propext, Classical.choice, Quot.sound}`).  Issue #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators Classical
open Finset

variable {m : ℕ} [NeZero m]

/-- **The diagonal (Wick) part of the resonance moment**: the sum over the whole nonzero filter of the
squared phase-product norm. -/
noncomputable def resonanceDiag (u : ZMod m → ℂ) (r : ℕ) : ℝ :=
  ∑ X ∈ (Finset.univ.filter (fun X : Fin r → ZMod m => ∀ i, X i ≠ 0)),
    ‖∏ i, u (X i)‖ ^ 2

/-- **`‖phaseSum u r c‖² = ∑_{X,Y in fiber c} conj(∏u X)·(∏u Y)` as a complex equality.**  The squared
norm of a complex sum expands to the conjugated double sum over the same fiber. -/
theorem normSq_phaseSum_eq_double (u : ZMod m → ℂ) (r : ℕ) (c : ZMod m) :
    ((‖phaseSum u r c‖ ^ 2 : ℝ) : ℂ)
      = ∑ X ∈ (Finset.univ.filter (fun X : Fin r → ZMod m =>
            (∀ i, X i ≠ 0) ∧ (∑ i, X i) = c)),
          ∑ Y ∈ (Finset.univ.filter (fun Y : Fin r → ZMod m =>
            (∀ i, Y i ≠ 0) ∧ (∑ i, Y i) = c)),
            (starRingEnd ℂ) (∏ i, u (X i)) * (∏ i, u (Y i)) := by
  unfold phaseSum
  have hcast : ((‖(∑ X ∈ (Finset.univ.filter (fun X : Fin r → ZMod m =>
        (∀ i, X i ≠ 0) ∧ (∑ i, X i) = c)), ∏ i, u (X i))‖ ^ 2 : ℝ) : ℂ)
      = (starRingEnd ℂ) (∑ X ∈ (Finset.univ.filter (fun X : Fin r → ZMod m =>
        (∀ i, X i ≠ 0) ∧ (∑ i, X i) = c)), ∏ i, u (X i))
        * (∑ X ∈ (Finset.univ.filter (fun X : Fin r → ZMod m =>
        (∀ i, X i ≠ 0) ∧ (∑ i, X i) = c)), ∏ i, u (X i)) := by
    rw [Complex.sq_norm]
    exact Complex.normSq_eq_conj_mul_self
  rw [hcast]
  rw [map_sum]
  exact Finset.sum_mul_sum _ _ _ _

/-- **Diagonal extraction of the resonance moment (the `Wick`-floor decomposition).**
`(T r : ℂ) = ∑_{X,Y : both nonzero, ∑X=∑Y} conj(∏u X)·(∏u Y)`.  Summing the fiberwise double sums over
all frequencies `c` merges the two per-fiber filters into the single *agreement relation* `∑X=∑Y`. -/
theorem resonanceMoment_eq_agreement_double (u : ZMod m → ℂ) (r : ℕ) :
    ((resonanceMoment u r : ℝ) : ℂ)
      = ∑ X ∈ (Finset.univ.filter (fun X : Fin r → ZMod m => ∀ i, X i ≠ 0)),
          ∑ Y ∈ (Finset.univ.filter (fun Y : Fin r → ZMod m =>
              (∀ i, Y i ≠ 0) ∧ (∑ i, Y i) = (∑ i, X i))),
            (starRingEnd ℂ) (∏ i, u (X i)) * (∏ i, u (Y i)) := by
  unfold resonanceMoment
  rw [Complex.ofReal_sum]
  rw [Finset.sum_congr rfl (fun c _ => normSq_phaseSum_eq_double u r c)]
  -- merge the outer c-sum into the X-filter (∀i,X i≠0), pinning ∑X = c on the inner Y-filter
  rw [← Finset.sum_fiberwise
        (s := Finset.univ.filter (fun X : Fin r → ZMod m => ∀ i, X i ≠ 0))
        (g := fun X : Fin r → ZMod m => ∑ i, X i)
        (f := fun X => ∑ Y ∈ (Finset.univ.filter (fun Y : Fin r → ZMod m =>
            (∀ i, Y i ≠ 0) ∧ (∑ i, Y i) = (∑ i, X i))),
          (starRingEnd ℂ) (∏ i, u (X i)) * (∏ i, u (Y i)))]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  refine Finset.sum_congr ?_ (fun X hX => ?_)
  · ext X
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · have hXc : (∑ i, X i) = c := (Finset.mem_filter.mp hX).2
    rw [hXc]

/-- **The diagonal value for unit-modulus phases is the Wick count `(m-1)^r`.**
`resonanceDiag u r = (m-1)^r` when `‖u a‖ = 1` for every nonzero `a`. -/
theorem resonanceDiag_unit (u : ZMod m → ℂ) (r : ℕ)
    (hu : ∀ a : ZMod m, a ≠ 0 → ‖u a‖ = 1) :
    resonanceDiag u r = ((m - 1 : ℕ) : ℝ) ^ r := by
  classical
  unfold resonanceDiag
  have hone : ∀ X ∈ (Finset.univ.filter (fun X : Fin r → ZMod m => ∀ i, X i ≠ 0)),
      ‖∏ i, u (X i)‖ ^ 2 = 1 := by
    intro X hX
    have hXne : ∀ i, X i ≠ 0 := (Finset.mem_filter.mp hX).2
    have : ‖∏ i, u (X i)‖ = 1 := by
      rw [norm_prod]
      refine Finset.prod_eq_one (fun i _ => ?_)
      exact hu (X i) (hXne i)
    rw [this, one_pow]
  rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- card of the all-nonzero filter = (m-1)^r
  have hcard : (Finset.univ.filter (fun X : Fin r → ZMod m => ∀ i, X i ≠ 0)).card
      = (m - 1) ^ r := by
    rw [show (Finset.univ.filter (fun X : Fin r → ZMod m => ∀ i, X i ≠ 0))
          = Fintype.piFinset (fun _ : Fin r => Finset.univ.filter (fun a : ZMod m => a ≠ 0)) by
        ext X; simp [Fintype.mem_piFinset]]
    rw [Fintype.card_piFinset_const]
    congr 1
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card]
  rw [hcard]; push_cast; ring

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.normSq_phaseSum_eq_double
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_eq_agreement_double
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceDiag_unit
