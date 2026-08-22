/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiffTraceLinearSumReframe

/-!
# CONSTRAINT — the L² reframe does NOT escape the pair sum: re-expanding `‖Σ Jphase‖²` is circular (#444)

**Door-(iv) Lane 3 constraint lemma (refutation-with-mechanism).**  The reframe
`_DiffTraceLinearSumReframe` re-expressed the variance-core open core as a bound on the L² mass of a
SINGLE complex number `Σ_T Jphase θ T`.  A tempting next move is to "attack" `‖Σ_T Jphase θ T‖²` by
some second-moment / energy method DIFFERENT from the pair sum.  This file proves that any such move
that simply RE-EXPANDS the square `‖Σ Jphase‖² = (Σ Jphase)·conj(Σ Jphase)` back into a double sum
over pairs lands EXACTLY on `FullTrace = #Rel + DiffTrace` — i.e. it returns to the SAME pair
correlation object (`OffDiagonalPairCancellation` of `_CreateWraparoundVariance`).  The L² reframe is
a genuine simplification of the STATEMENT, but it does NOT manufacture a new attackable quantity by
re-squaring: the moment/energy face of the L² object is the original pair sum, closing the loop.

This is the precise honesty boundary on the variance route: the reframe is a citable reduction, not
an escape from the second-moment wall.  Consistent with §6 of #444 (additive-moment/energy bounds
proven non-proving) and the door-(i) moment=BGK cap.

## The mechanism

`‖Σ_T Jphase θ T‖² = Complex.normSq (Σ Jphase) = (Σ Jphase)·conj(Σ Jphase)`.  By
`fullTrace_eq_mul_conj_sum` (`_DiffTracePlancherelFloor`) this is exactly `FullTrace θ Rel`, and by
`fullTrace_eq_card_add_diffTrace` (`_DiffTraceDiagonalExtraction`) `FullTrace = #Rel + DiffTrace`.  So
```
   (‖Σ_T Jphase θ T‖² : ℂ)  =  FullTrace θ Rel  =  #Rel  +  DiffTrace θ Rel.
```
Re-expanding the reframed L² object reproduces the off-diagonal first moment `DiffTrace` (= the pair
sum).  Any "new" energy bound obtained by expanding the square is the OLD pair-correlation bound.

## What this file PROVES (axiom-clean, no `sorry`)

* `normSq_sum_eq_fullTrace` — `(‖Σ Jphase‖² : ℂ) = FullTrace θ Rel` (the re-expansion target);
* `normSq_sum_eq_card_add_diffTrace` — `(‖Σ Jphase‖² : ℂ) = #Rel + DiffTrace θ Rel` (lands on the
  pair sum);
* `reframe_reexpansion_circular` — the explicit circularity statement: the reframed L² object's real
  part equals `#Rel + (DiffTrace).re`, so bounding it by re-expansion is bounding `DiffTrace.re`
  (the original open core) — no new content;
* `firstMomentDiffCancellation_iff_fullTrace_re_le_card_add` — the equivalent unpunctured full-trace
  upper-bound form: `FirstMomentDiffCancellation θ Rel S ↔ (FullTrace θ Rel).re ≤ #Rel + S`.

NO CORE / cancellation / completion / moment-saving / capacity claim: this is a Lane-3 constraint
lemma pinning that the L² reframe does not escape the pair-correlation second-moment wall by
re-squaring.  #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.DiffTraceReframeCircularity

open Finset ComplexConjugate
open ArkLib.ProximityGap.Frontier.NextDifferenceVariety
open ArkLib.ProximityGap.Frontier.DiffTraceDiagonalExtraction
open ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloor

variable {R : Type*} [AddCommGroup R] {r : ℕ} {θ : R → ℂ} [DecidableEq (Fin r → R)]

/-- **`normSq_sum_eq_fullTrace`** — re-expanding the reframed L² object lands on the full pair-sum
trace: `(‖Σ_T Jphase θ T‖² : ℂ) = FullTrace θ Rel`.  (Inverse of the Plancherel identity.) -/
theorem normSq_sum_eq_fullTrace (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    (Complex.normSq (∑ T ∈ Rel, Jphase θ T) : ℂ) = FullTrace θ Rel :=
  (fullTrace_eq_normSq_sum hmul hone hunit Rel).symm

/-- **`normSq_sum_eq_card_add_diffTrace`** — the reframed L² object re-expands to `#Rel` plus the
off-diagonal first moment (the pair sum): `(‖Σ Jphase‖² : ℂ) = #Rel + DiffTrace θ Rel`.  The energy
face of the L² object IS the original pair-correlation object. -/
theorem normSq_sum_eq_card_add_diffTrace (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    (Complex.normSq (∑ T ∈ Rel, Jphase θ T) : ℂ) = (Rel.card : ℂ) + DiffTrace θ Rel := by
  rw [normSq_sum_eq_fullTrace hmul hone hunit Rel,
      fullTrace_eq_card_add_diffTrace hmul hone hunit Rel]

/-- **`reframe_reexpansion_circular`** — THE circularity constraint.  Taking real parts, the reframed
L² mass equals `#Rel + (DiffTrace).re`:
```
        ‖Σ_T Jphase θ T‖²  =  #Rel  +  (DiffTrace θ Rel).re.
```
So bounding the reframed L² object by re-expanding the square is, verbatim, bounding the off-diagonal
first moment `(DiffTrace).re` (the original open core / pair-correlation sum).  The reframe does not
create a new attackable energy quantity; its moment face is the wall itself. -/
theorem reframe_reexpansion_circular (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    Complex.normSq (∑ T ∈ Rel, Jphase θ T) = (Rel.card : ℝ) + (DiffTrace θ Rel).re := by
  have h := normSq_sum_eq_card_add_diffTrace hmul hone hunit Rel
  have hre := congrArg Complex.re h
  simpa [Complex.add_re, Complex.natCast_re, Complex.ofReal_re] using hre

/-- **`fullTrace_re_eq_card_add_diffTrace_re`** — the unpunctured full trace has real part equal to
`#Rel + (DiffTrace).re`.  This is the diagonal-extraction identity after taking real parts. -/
theorem fullTrace_re_eq_card_add_diffTrace_re (hmul : ∀ a b, θ (a + b) = θ a * θ b)
    (hone : θ 0 = 1) (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    (FullTrace θ Rel).re = (Rel.card : ℝ) + (DiffTrace θ Rel).re := by
  have h := fullTrace_eq_card_add_diffTrace hmul hone hunit Rel
  have hre := congrArg Complex.re h
  simpa [Complex.add_re, Complex.natCast_re, Complex.ofReal_re] using hre

/-- **`firstMomentDiffCancellation_iff_fullTrace_re_le_card_add`** — exact unpunctured-trace form of
the named open core.  Bounding the real part of the full trace by `#Rel + S` is equivalent to bounding
the off-diagonal first moment by `S`, because the diagonal contributes exactly `#Rel`. -/
theorem firstMomentDiffCancellation_iff_fullTrace_re_le_card_add
    (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) (S : ℝ) :
    FirstMomentDiffCancellation θ Rel S ↔ (FullTrace θ Rel).re ≤ (Rel.card : ℝ) + S := by
  unfold FirstMomentDiffCancellation
  rw [fullTrace_re_eq_card_add_diffTrace_re hmul hone hunit Rel]
  constructor <;> intro h <;> linarith

/-- Producer direction for the unpunctured full-trace form. -/
theorem firstMomentDiffCancellation_of_fullTrace_re_le_card_add
    (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) (S : ℝ)
    (h : (FullTrace θ Rel).re ≤ (Rel.card : ℝ) + S) :
    FirstMomentDiffCancellation θ Rel S :=
  (firstMomentDiffCancellation_iff_fullTrace_re_le_card_add hmul hone hunit Rel S).mpr h

end ArkLib.ProximityGap.Frontier.DiffTraceReframeCircularity

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceReframeCircularity.normSq_sum_eq_fullTrace
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceReframeCircularity.normSq_sum_eq_card_add_diffTrace
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceReframeCircularity.reframe_reexpansion_circular
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceReframeCircularity.fullTrace_re_eq_card_add_diffTrace_re
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceReframeCircularity.firstMomentDiffCancellation_iff_fullTrace_re_le_card_add
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceReframeCircularity.firstMomentDiffCancellation_of_fullTrace_re_le_card_add
