/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiffTraceDiagonalExtraction

/-!
# EXTEND — the variance-core Plancherel perfect-square floor `DiffTrace.re ≥ −#Rel` (#444)

**Frontier-movement extension of `_DiffTraceDiagonalExtraction`.**  That file proved the
diagonal-extraction identity `FullTrace θ Rel = #Rel + DiffTrace θ Rel`, where
`FullTrace θ Rel = Σ_T Σ_{T'∈Rel} Jphase θ (diffTuple T T')` is the FULL (unpunctured) first moment
over the difference variety.  This file pins the structural fact that makes `FullTrace` a clean
object: it is a **perfect square modulus**, hence a NON-NEGATIVE REAL, which gives the exact,
explicit, UNCONDITIONAL lower floor for the variance-core off-diagonal trace.

## The mechanism — `FullTrace` is `‖Σ_T Jphase θ T‖²`

By the summand reduction `pairCorr_eq_diff` of `_NextDifferenceVariety`, every term of the full
double sum factors as `Jphase θ (diffTuple T T') = Jphase θ T · conj (Jphase θ T')`.  Summing over
the full product `Rel × Rel` (NO puncture) factors the double sum (`Finset.sum_mul_sum`):
```
   FullTrace θ Rel = Σ_T Σ_{T'} Jphase θ T · conj (Jphase θ T')
                   = (Σ_T Jphase θ T) · conj (Σ_{T'} Jphase θ T')
                   = (Σ_T Jphase θ T) · conj (Σ_T Jphase θ T)
                   = ‖Σ_T Jphase θ T‖²   ≥ 0.                  (fullTrace_eq_normSq_sum)
```
This is the Plancherel / completeness identity for the variance core: the full point count IS the
squared modulus of the linear phase sum.

## The exact floor — `diffTrace_re_ge_neg_card`

Combining `FullTrace = ‖Σ Jphase‖² ≥ 0` with the diagonal extraction
`FullTrace = #Rel + DiffTrace`:
```
        DiffTrace θ Rel . re  =  ‖Σ_T Jphase θ T‖²  −  #Rel   ≥   −#Rel.
```
So the off-diagonal first moment can drop AT MOST `#Rel` below zero — an exact, explicit,
unconditional lower bound.  This is the **trivial/floor side**: it is NOT the open upper bound the
prize needs (`DiffTrace.re ≤ S` with `S` sub-Poisson stays open), but it shows the variance-core
object is a SHIFTED NON-NEGATIVE square: `DiffTrace.re + #Rel = ‖Σ Jphase‖² ≥ 0`.  Any future upper
bound therefore controls `‖Σ Jphase‖²` in `[0, ?]`; the floor end is closed here.

## Probe

`scripts/probes/probe_dooriv_fulltrace_perfect_square.py` (proper `μ_n < F_p^*`, `p ≫ n³`, never
`n=q−1`; `n=16,32,64`, `β∈{4,4.5}`, `r∈{3,4,5}`): `|FullTrace − ‖Σ Jphase‖²| ≤ 3·10⁻¹²`,
`|Im FullTrace| ≤ 3·10⁻¹²`, and `DiffTrace.re + #Rel = ‖Σ Jphase‖² ≥ 0` on every config.

## What this file PROVES (axiom-clean, no `sorry`)

* `fullTrace_eq_mul_conj_sum` — `FullTrace = (Σ Jphase)·conj(Σ Jphase)` (the factorization);
* `fullTrace_eq_normSq_sum` — `FullTrace = (‖Σ Jphase‖² : ℂ)` (perfect square modulus);
* `fullTrace_re_nonneg` / `fullTrace_im_zero` — `FullTrace` is a non-negative real;
* `diffTrace_re_eq_normSq_sub_card` — `DiffTrace.re = ‖Σ Jphase‖² − #Rel` (exact);
* `diffTrace_re_ge_neg_card` — the exact unconditional floor `DiffTrace.re ≥ −#Rel`;
* `diffTrace_re_add_card_nonneg` — `DiffTrace.re + #Rel ≥ 0` (the shifted-square form).

NO CORE / cancellation / completion / moment-saving / capacity claim: this is the FLOOR side
(the prize needs the open UPPER bound).  Structural Plancherel identity + the explicit lower
envelope of the variance-core object.  #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloor

open Finset ComplexConjugate
open ArkLib.ProximityGap.Frontier.NextDifferenceVariety
open ArkLib.ProximityGap.Frontier.DiffTraceDiagonalExtraction

variable {R : Type*} [AddCommGroup R] {r : ℕ} {θ : R → ℂ} [DecidableEq (Fin r → R)]

/-! ## §1 The full trace factors as a perfect square modulus -/

/-- **`fullTrace_eq_mul_conj_sum`** — the full (unpunctured) first moment factors as the linear
phase sum times its conjugate: `FullTrace θ Rel = (Σ_T Jphase θ T) · conj (Σ_T Jphase θ T)`.  Each
term `Jphase θ (diffTuple T T')` reduces to `Jphase θ T · conj (Jphase θ T')` (`pairCorr_eq_diff`),
and the full product double sum factors (`Finset.sum_mul_sum`). -/
theorem fullTrace_eq_mul_conj_sum (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    FullTrace θ Rel
      = (∑ T ∈ Rel, Jphase θ T) * conj (∑ T' ∈ Rel, Jphase θ T') := by
  unfold FullTrace
  -- replace each diff-tuple phase by the factored pair summand
  have hcongr : ∀ T ∈ Rel, ∀ T' ∈ Rel,
      Jphase θ (diffTuple T T') = Jphase θ T * conj (Jphase θ T') := by
    intro T _ T' _; exact (pairCorr_eq_diff hmul hone hunit T T').symm
  rw [Finset.sum_congr rfl (fun T hT =>
        Finset.sum_congr rfl (fun T' hT' => hcongr T hT T' hT'))]
  rw [map_sum, Finset.sum_mul_sum]

/-- **`fullTrace_eq_normSq_sum`** — the full trace is the squared modulus of the linear phase sum:
`FullTrace θ Rel = (‖Σ_T Jphase θ T‖² : ℂ)`.  A non-negative real (Plancherel identity). -/
theorem fullTrace_eq_normSq_sum (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    FullTrace θ Rel = (Complex.normSq (∑ T ∈ Rel, Jphase θ T) : ℂ) := by
  rw [fullTrace_eq_mul_conj_sum hmul hone hunit Rel, Complex.mul_conj]

/-! ## §2 The full trace is a non-negative real -/

/-- **`fullTrace_re_nonneg`** — `0 ≤ (FullTrace θ Rel).re`. -/
theorem fullTrace_re_nonneg (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    0 ≤ (FullTrace θ Rel).re := by
  rw [fullTrace_eq_normSq_sum hmul hone hunit Rel, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

/-- **`fullTrace_im_zero`** — `(FullTrace θ Rel).im = 0` (consistent with the diagonal-inclusive
realness; here directly from the perfect-square form). -/
theorem fullTrace_im_zero (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    (FullTrace θ Rel).im = 0 := by
  rw [fullTrace_eq_normSq_sum hmul hone hunit Rel, Complex.ofReal_im]

/-! ## §3 The exact Plancherel floor on the variance-core off-diagonal trace -/

/-- **`diffTrace_re_eq_normSq_sub_card`** — the exact value of the off-diagonal first-moment real
part: `(DiffTrace θ Rel).re = ‖Σ_T Jphase θ T‖² − #Rel`.  From `FullTrace = #Rel + DiffTrace`
(diagonal extraction) and `FullTrace = ‖Σ Jphase‖²` (Plancherel), taking real parts. -/
theorem diffTrace_re_eq_normSq_sub_card (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    (DiffTrace θ Rel).re = Complex.normSq (∑ T ∈ Rel, Jphase θ T) - (Rel.card : ℝ) := by
  have hdiag : DiffTrace θ Rel = FullTrace θ Rel - (Rel.card : ℂ) :=
    diffTrace_eq_fullTrace_sub_card hmul hone hunit Rel
  rw [hdiag, fullTrace_eq_normSq_sum hmul hone hunit Rel]
  simp [Complex.sub_re, Complex.ofReal_re, Complex.natCast_re]

/-- **`diffTrace_re_ge_neg_card`** — the exact unconditional FLOOR: `−#Rel ≤ (DiffTrace θ Rel).re`.
The off-diagonal first moment can drop at most `#Rel` below zero, because
`(DiffTrace).re + #Rel = ‖Σ Jphase‖² ≥ 0`.  This is the trivial/floor side, NOT the open prize
upper bound. -/
theorem diffTrace_re_ge_neg_card (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    -(Rel.card : ℝ) ≤ (DiffTrace θ Rel).re := by
  rw [diffTrace_re_eq_normSq_sub_card hmul hone hunit Rel]
  have := Complex.normSq_nonneg (∑ T ∈ Rel, Jphase θ T)
  linarith

/-- **`diffTrace_re_add_card_nonneg`** — the shifted-square form: `0 ≤ (DiffTrace θ Rel).re + #Rel`,
equivalently `(DiffTrace).re + #Rel = ‖Σ Jphase‖² ≥ 0`.  Any future upper bound on the variance-core
object thus controls a NON-NEGATIVE shifted square in `[0, ?]`; the lower end is closed here. -/
theorem diffTrace_re_add_card_nonneg (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    0 ≤ (DiffTrace θ Rel).re + (Rel.card : ℝ) := by
  have := diffTrace_re_ge_neg_card hmul hone hunit Rel
  linarith

end ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloor

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloor.fullTrace_eq_mul_conj_sum
#print axioms ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloor.fullTrace_eq_normSq_sum
#print axioms ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloor.fullTrace_re_nonneg
#print axioms ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloor.diffTrace_re_eq_normSq_sub_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloor.diffTrace_re_ge_neg_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloor.diffTrace_re_add_card_nonneg
