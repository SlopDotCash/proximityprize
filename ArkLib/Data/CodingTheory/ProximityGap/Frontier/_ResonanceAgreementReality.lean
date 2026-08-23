/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceDiagonalExtraction

/-!
# The agreement double sum is REAL — the resonance off-diagonal is a real object (door-(iv), Lane 3)

`_ResonanceDiagonalExtraction` proved the exact identity

> `((resonanceMoment u r : ℝ) : ℂ) = agreementDouble u r`

where `agreementDouble u r` is the complex double sum over agreeing nonzero tuples `(X, Y)`
(`∑X = ∑Y`) of `conj(∏ u X) · (∏ u Y)`, and named the diagonal `X = Y` as the Wick floor.

This file pins a structural fact about that double sum that is **independent of the
`resonanceMoment`-is-real cast**: the agreement double sum is **self-conjugate** under the
`(X, Y) ↦ (Y, X)` swap, hence it is *manifestly real as a sum*.  Conjugating the summand turns the
`(X, Y)` term into the `(Y, X)` term, and the agreement relation `∑X = ∑Y` is symmetric, so the
reindexing closes:

> `conj (agreementDouble u r) = agreementDouble u r`            (`agreementDouble_conj_eq`)
> `(agreementDouble u r).im = 0`                                (`agreementDouble_im_eq_zero`)

Consequently the **off-diagonal** `resonanceOffDiag u r := agreementDouble u r − (diagonal : ℂ)`
(the `X ≠ Y`, `∑X = ∑Y` part — the single open object of the prize) is itself a **real** quantity,
and for unit-modulus phases it sits exactly `(m-1)^r` below the resonance moment:

> `(resonanceOffDiag u r).im = 0`                              (`resonanceOffDiag_im_eq_zero`)
> `resonanceMoment u r = (m-1)^r + (resonanceOffDiag u r).re`
>                                                   (`resonanceMoment_eq_wick_add_offDiag_re`)

**Meaning (constraint, Lane 3).**  The `√`-cancellation question is entirely about the *real*
a *real* quantity — the off-diagonal cannot be attacked or escape through a complex/imaginary phase:
its imaginary part is structurally zero.  Any prize bound on the off-diagonal is a bound on a real
number `(resonanceOffDiag u r).re = T(r) − (m-1)^r`, with no hidden complex slack.  This is a
honesty-grade locking of the off-diagonal object, **not** a bound on it — the off-diagonal stays
OPEN.  No CORE / cancellation / completion / moment / anti-concentration / capacity claim.

Self-contained leaf over `_ResonanceDiagonalExtraction`.  Axiom-clean
(`{propext, Classical.choice, Quot.sound}`).  Issue #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators Classical
open Finset

variable {m : ℕ} [NeZero m]

/-- **The agreement double sum** (the RHS of `resonanceMoment_eq_agreement_double`): the complex
double sum over agreeing nonzero tuples `(X, Y)` with `∑X = ∑Y` of `conj(∏ u X) · (∏ u Y)`. -/
noncomputable def agreementDouble (u : ZMod m → ℂ) (r : ℕ) : ℂ :=
  ∑ X ∈ (Finset.univ.filter (fun X : Fin r → ZMod m => ∀ i, X i ≠ 0)),
    ∑ Y ∈ (Finset.univ.filter (fun Y : Fin r → ZMod m =>
        (∀ i, Y i ≠ 0) ∧ (∑ i, Y i) = (∑ i, X i))),
      (starRingEnd ℂ) (∏ i, u (X i)) * (∏ i, u (Y i))

/-- The agreement double sum is exactly `((resonanceMoment u r : ℝ) : ℂ)` (restating the diagonal
extraction in terms of the named `agreementDouble`). -/
theorem agreementDouble_eq_resonanceMoment (u : ZMod m → ℂ) (r : ℕ) :
    agreementDouble u r = ((resonanceMoment u r : ℝ) : ℂ) :=
  (resonanceMoment_eq_agreement_double u r).symm

/-- **Self-conjugacy of the agreement double sum.** Conjugating the summand sends the `(X, Y)` term
to the `(Y, X)` term, and the agreement relation `∑X = ∑Y` is symmetric, so the `(X, Y) ↦ (Y, X)`
swap reindexes the conjugated sum back to itself:
`conj (agreementDouble u r) = agreementDouble u r`. -/
theorem agreementDouble_conj_eq (u : ZMod m → ℂ) (r : ℕ) :
    (starRingEnd ℂ) (agreementDouble u r) = agreementDouble u r := by
  classical
  unfold agreementDouble
  -- conj of a double sum = double sum of conj
  rw [map_sum]
  simp only [map_sum, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  -- now: ∑_X ∑_{Y : ∑Y=∑X} (∏uY) * conj(∏uX)  -- want to reindex to the original by swapping names
  -- Convert the iterated sum to a sum over the product filter, swap, and convert back.
  rw [Finset.sum_sigma', Finset.sum_sigma']
  -- reindex by the involution σ : ⟨X, Y⟩ ↦ ⟨Y, X⟩
  refine Finset.sum_nbij'
    (i := fun p => ⟨p.2, p.1⟩)
    (j := fun p => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨X, Y⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨hX, hY, hsum⟩ := hp
    exact ⟨hY, hX, hsum.symm⟩
  · rintro ⟨X, Y⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨hX, hY, hsum⟩ := hp
    exact ⟨hY, hX, hsum.symm⟩
  · rintro ⟨X, Y⟩ _; rfl
  · rintro ⟨X, Y⟩ _; rfl
  · rintro ⟨X, Y⟩ _
    -- summand at ⟨Y, X⟩ on the conjugated side: (∏uX) * conj(∏uY)
    -- summand at ⟨X, Y⟩ on the original side: conj(∏uX) * (∏uY)
    ring

/-- **The agreement double sum is real**: its imaginary part vanishes (from self-conjugacy). -/
theorem agreementDouble_im_eq_zero (u : ZMod m → ℂ) (r : ℕ) :
    (agreementDouble u r).im = 0 := by
  have h := agreementDouble_conj_eq u r
  rw [Complex.conj_eq_iff_im] at h
  exact h

/-- **The off-diagonal of the resonance moment** (the `X ≠ Y`, `∑X = ∑Y` agreement term): the full
agreement double sum minus the diagonal (Wick) part, as a complex number. -/
noncomputable def resonanceOffDiag (u : ZMod m → ℂ) (r : ℕ) : ℂ :=
  agreementDouble u r - ((resonanceDiag u r : ℝ) : ℂ)

/-- **The off-diagonal is real.** Both the agreement double sum and the (real-cast) diagonal have
zero imaginary part, so does their difference. -/
theorem resonanceOffDiag_im_eq_zero (u : ZMod m → ℂ) (r : ℕ) :
    (resonanceOffDiag u r).im = 0 := by
  unfold resonanceOffDiag
  rw [Complex.sub_im, agreementDouble_im_eq_zero, Complex.ofReal_im, sub_zero]

/-- **Real-part decomposition of the resonance moment for unit-modulus phases.**
`resonanceMoment u r = (m-1)^r + (resonanceOffDiag u r).re`: the Wick floor `(m-1)^r` plus the real
part of the (real) agreement off-diagonal — the single open object of the prize. -/
theorem resonanceMoment_eq_wick_add_offDiag_re (u : ZMod m → ℂ) (r : ℕ)
    (hu : ∀ a : ZMod m, a ≠ 0 → ‖u a‖ = 1) :
    resonanceMoment u r = ((m - 1 : ℕ) : ℝ) ^ r + (resonanceOffDiag u r).re := by
  have hagr : (agreementDouble u r).re = resonanceMoment u r := by
    rw [agreementDouble_eq_resonanceMoment, Complex.ofReal_re]
  have hoff : (resonanceOffDiag u r).re
      = (agreementDouble u r).re - resonanceDiag u r := by
    unfold resonanceOffDiag
    rw [Complex.sub_re, Complex.ofReal_re]
  rw [hoff, hagr, resonanceDiag_unit u r hu]
  ring

end ArkLib.ProximityGap.GaussPhaseResonance

#print axioms ArkLib.ProximityGap.GaussPhaseResonance.agreementDouble_eq_resonanceMoment
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.agreementDouble_conj_eq
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.agreementDouble_im_eq_zero
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceOffDiag_im_eq_zero
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_eq_wick_add_offDiag_re
