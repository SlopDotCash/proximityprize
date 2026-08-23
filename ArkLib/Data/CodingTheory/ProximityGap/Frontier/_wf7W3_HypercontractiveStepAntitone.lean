/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf6F1_gaussian_step_telescope

/-!
# W3: the hypercontractive **step-ratio antitonicity** ladder ⟹ the Gaussian step-law (#444, wf-W3)

## The lead (sub-Gaussian / hypercontractivity on the dyadic cube)

The DC-subtracted Gauss periods `{η_b/√n}_{b≠0}` of the dyadic subgroup `μ_n` (`n = 2^μ`) are
**sub-Gaussian** with variance proxy ≈ `n` (the Gaussian value). The W3 strategy is Bonami–Beckner /
log-Sobolev hypercontractivity on the dyadic structure: a sub-Gaussian variable's even-moment
sequence `M_{2r}` obeys the Gaussian step-law `M_{2(r+1)} ≤ (2r+1)·s·M_{2r}` (`s = n` the proxy),
which the in-tree telescope `WF6F1.gaussian_moment_bound_of_stepLaw` converts to the full Wick bound
`M_{2r} ≤ (2r-1)‼·s^r`, i.e. the floor `A_r ≤ Wick_r`.

This file does **not** re-prove the telescope. It supplies the **sharper hypercontractive reduction
of the step-law itself**, the W3 deliverable. Define the *normalized* step ratio

> `R(r) := M(r+1) / ((2r+1)·s·M(r))`     (the cumulant / hypercontractive ratio; `R ≡ 1` for `N(0,s)`).

The Gaussian step-law is exactly `R(r) ≤ 1 ∀r`. Lane-W3 exact numerics
(`scripts/probes/probe_wf7W3_*` / `scripts/probes/rust/`, exact `cos`-period sums over `F_p`,
`β ≈ 4..5.3`, depth `r ≈ 1.6·ln q`, `n = 16..256`) measured the decisive structural fact:

* `R(r)` is **antitone** (monotone non-increasing) in `r` across the whole prize regime, and its
  supremum is attained at `r = 1`, where `R(1) = M_4/(3·s·M_2) ≤ 0.99 < 1`.  (Equivalently, the
  `ψ₂`-moment constant `K_eff(r) = (M_{2r}/[(2r-1)‼ s^r])^{1/r}` is monotone decreasing with
  `sup_r K_eff(r) = K_eff(1) = M_2/s ≈ 1`.)

So the open step-law `R(r) ≤ 1 ∀r` reduces to TWO hypercontractive facts:
  (W3-base)  `R(1) ≤ 1`  — the **second-and-fourth-moment** inequality `M_4 ≤ 3·s·M_2` (a fixed, finite
             check; the `r=1` Parseval/hypercontractive base, NOT a deep-moment statement); and
  (W3-anti)  `R` antitone — the **cumulant-ratio monotonicity**, the genuine log-Sobolev /
             Bonami–Beckner content of the dyadic cube.

This is **sharper** than the prior per-step `GaussianStepLaw` (all-`r`) and than
`WickMonotonicityReduction.WickMonotonicity`: it pins the open content to a *monotonicity of one
explicit ratio* anchored at a *single base inequality*, exactly the hypercontractive object.

## What this file proves (axiom-clean, pure-math ladder)

* `NormStepRatio` — the normalized step ratio `R(r)` as a sequence (guarded against `M r = 0`).
* `StepRatioAntitone` — the named hypercontractive hypothesis: `R(r+1) ≤ R(r)` for `r ≥ 1`.
* `stepLaw_of_antitone_base` — **THE LADDER** (axiom-clean): from positivity of `M`, the base
  `R(1) ≤ 1` and `StepRatioAntitone`, derive the full `WF6F1.GaussianStepLaw M s`.
* `gaussian_moment_bound_of_antitone_base` — composes the ladder with the in-tree telescope to land
  `M r ≤ (2r-1)‼·s^r` for ALL `r` from `[R(1)≤1] + [R antitone]` (+ base `M 0 ≤ 1`).

Honest scope (the wall): `(W3-anti)` (the cumulant-ratio antitonicity) is the remaining OPEN analytic
input — it is *empirically true and β-conditional* (robust for prize `β ≈ 5.27`; the same
small-`β ≈ 2` violation flagged in F1 applies). This file is the **deductive producer** turning the
open floor into that single monotonicity, NOT a closure. The base `(W3-base)` `M_4 ≤ 3 s M_2` is a
finite hypercontractive fact (the `r=1` face, `A_1 < n` is `SecondMomentExact.base_case_strict` for
the *un-normalized* second moment; the fourth-moment cap is the new finite check).

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #444, lane wf-W3.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.WF7W3

open ArkLib.ProximityGap.Frontier.WF6F1

/-- The **normalized Gaussian step ratio** of a moment sequence `M` with variance proxy `s`:
`R(r) = M(r+1) / ((2r+1)·s·M(r))`. For a real Gaussian `N(0,s)` this is identically `1`
(`M(r)=(2r-1)‼ s^r`); the hypercontractive lead asserts the dyadic periods have `R ≤ 1`. -/
noncomputable def NormStepRatio (M : ℕ → ℝ) (s : ℝ) (r : ℕ) : ℝ :=
  M (r + 1) / ((2 * r + 1 : ℝ) * s * M r)

/-- The **hypercontractive antitonicity** hypothesis (W3-anti): the normalized step ratio is
monotone non-increasing from `r = 1` on, `R(r+1) ≤ R(r)` for every `r ≥ 1`. This is the cumulant-ratio
/ log-Sobolev content measured to hold across the prize regime. -/
def StepRatioAntitone (M : ℕ → ℝ) (s : ℝ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → NormStepRatio M s (r + 1) ≤ NormStepRatio M s r

/-- A normalized step ratio bounded by `1` *is* a Gaussian step at that order: `R(r) ≤ 1` unfolds to
`M(r+1) ≤ (2r+1)·s·M(r)` whenever `M r > 0` and `(2r+1)·s ≥ 0`. -/
theorem step_of_normStepRatio_le_one {M : ℕ → ℝ} {s : ℝ} {r : ℕ}
    (hsr : 0 < (2 * r + 1 : ℝ) * s) (hMr : 0 < M r)
    (hR : NormStepRatio M s r ≤ 1) :
    M (r + 1) ≤ (2 * r + 1 : ℝ) * s * M r := by
  have hden : 0 < (2 * r + 1 : ℝ) * s * M r := mul_pos hsr hMr
  -- R(r) ≤ 1 ↔ M(r+1) ≤ den (multiply both sides by den > 0)
  rw [NormStepRatio, div_le_one hden] at hR
  exact hR

/-- **THE HYPERCONTRACTIVE LADDER.** With `s > 0` and `M r > 0` for all `r`, the base `R(1) ≤ 1` and
the antitonicity `StepRatioAntitone` together give `R(r) ≤ 1` for every `r ≥ 1`, hence the full
`GaussianStepLaw` for `r ≥ 1`. (At `r = 0` the step `M 1 ≤ 1·s·M 0` is the variance base, supplied
separately; see `gaussian_moment_bound_of_antitone_base`.)

This is the W3 reduction: the open all-`r` step-law collapses to ONE base inequality + ONE
monotonicity, the natural hypercontractive object. Axiom-clean. -/
theorem normStepRatio_le_one_of_antitone_base {M : ℕ → ℝ} {s : ℝ}
    (hbase : NormStepRatio M s 1 ≤ 1)
    (hanti : StepRatioAntitone M s) :
    ∀ r : ℕ, 1 ≤ r → NormStepRatio M s r ≤ 1 := by
  intro r hr
  induction r with
  | zero => exact absurd hr (by norm_num)
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · -- k = 0, so k + 1 = 1: this is the base
      subst hk; exact hbase
    · -- k ≥ 1: use antitonicity step then IH
      exact le_trans (hanti k hk) (ih hk)

/-- **W3 end-to-end via the in-tree telescope.** From positivity, the variance base
`M 1 ≤ s·M 0`, the hypercontractive base `R(1) ≤ 1`, the antitonicity `StepRatioAntitone`, and
`M 0 ≤ 1`, the full sub-Gaussian Wick bound `M r ≤ (2r-1)‼·s^r` holds for ALL `r`.

Mechanism: the ladder `normStepRatio_le_one_of_antitone_base` gives `R(r) ≤ 1 ∀ r ≥ 1`, i.e. the
Gaussian step at every `r ≥ 1`; together with the `r = 0` variance step this is the full
`WF6F1.GaussianStepLaw`, which the proven telescope `WF6F1.gaussian_moment_bound_of_stepLaw`
converts to the Wick bound. The open content is now exactly `(W3-base) R(1) ≤ 1` (finite) and
`(W3-anti) StepRatioAntitone` (the cumulant-ratio monotonicity). -/
theorem gaussian_moment_bound_of_antitone_base {M : ℕ → ℝ} {s : ℝ}
    (hs : 0 < s) (hM : ∀ r, 0 < M r)
    (hvar : M 1 ≤ s * M 0)
    (hbase : NormStepRatio M s 1 ≤ 1)
    (hanti : StepRatioAntitone M s)
    (hM0 : M 0 ≤ 1) :
    ∀ r : ℕ, M r ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * s ^ r := by
  -- assemble the full Gaussian step-law for all r
  have hRle : ∀ r : ℕ, 1 ≤ r → NormStepRatio M s r ≤ 1 :=
    normStepRatio_le_one_of_antitone_base hbase hanti
  have hstep : GaussianStepLaw M s := by
    intro r
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · -- r = 0: the variance step  M 1 ≤ (2·0+1)·s·M 0 = s·M 0
      subst hr0; simpa using hvar
    · -- r ≥ 1: from R(r) ≤ 1
      have hsr : 0 < (2 * r + 1 : ℝ) * s := by positivity
      exact step_of_normStepRatio_le_one hsr (hM r) (hRle r hrpos)
  exact gaussian_moment_bound_of_stepLaw (le_of_lt hs) (fun r => le_of_lt (hM r)) hM0 hstep

end ArkLib.ProximityGap.Frontier.WF7W3

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.WF7W3.normStepRatio_le_one_of_antitone_base
#print axioms ArkLib.ProximityGap.Frontier.WF7W3.gaussian_moment_bound_of_antitone_base
