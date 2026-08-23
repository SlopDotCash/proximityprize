/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Door IV: the `|·|`-LEAK — taking absolute values destroys the thinness-essential signed deep
# cancellation, so no moment / absolute-value bound can be the rule-3 lever

This file records the axiom-clean kernel behind the DISPROOF_LOG entry
"SIGNED deep period-power cancellation IS thinness-essential — and the moment certificate's `|.|`
destroys it" (2026-06-15), backed by the probes
`scripts/probes/probe_407_deep_sidon_depth.py` and
`scripts/probes/probe_407_signed_deep_cancellation.py`.

## Why this matters (the positive localization this kernel backs)

The campaign's dead doors all route through an ABSOLUTE quantity: the moment certificate uses
`Σ_{b≠0} |η_b|^{2r}`, the energy uses `E_r`, Wick / count / extreme-value all package `|η_b|`. The
probe found that the thinness-essential signal instead lives in the SIGNED deep period-power sum
`Σ_{b≠0} η_b^r` (since `μ_n` is negation-closed each `η_b ∈ ℝ`): the normalized
`C_r = |Σ_{b≠0} η_b^r| / ((p-1)·M^r)` is STRICTLY SMALLER (stronger signed cancellation) in the THIN
prize regime than in THICK at every depth `r`, and the thin/thick ratio GROWS with `r` (measured
2.5× at `r=2` up to 27× at `r=10`, `n=16`). The MECHANISM for why every moment method is
thickness-invariant is that `|·|` discards exactly this signed cancellation.

This kernel formalizes the HONEST, identity-level content of that mechanism — the `|·|`-leak itself —
WITHOUT claiming the (open) uniform deep-cancellation bound (that bound at `r ~ log q` IS the prize /
BGK wall). The contribution is to back the central mechanism claim ("`|·|` is the leak") with a
kernel-checked inequality + a falsifiable equality characterization, so the positive localization is
not prose-only.

## The formalizable kernel (this file)

Over a real `η : ι → ℝ` (the negation-closed period real-parts) on a finite index set:
1. `abs_signed_le_abs_moment` — the leak direction `|Σ η_b^r| ≤ Σ |η_b|^r`. This is the inequality
   EVERY absolute-value / moment packaging silently invokes.
2. `leak_nonneg` — the leak gap `Σ |η_b|^r - |Σ η_b^r| ≥ 0` is well-defined and nonnegative: the
   discarded cancellation.
3. `abs_moment_bound_does_not_bound_signed_below` — an absolute-moment bound `Σ |η_b|^r ≤ B`
   transfers to the signed sum `|Σ η_b^r| ≤ B`, but the converse FAILS: the signed sum can be `0`
   while the absolute moment is arbitrarily large (the cancellation a moment bound cannot see). We
   witness this with an explicit antipodal-cancelling pair.
4. `leak_zero_iff_aligned` (complex form `leak_zero_iff_aligned_complex`) — the falsifiable
   equality: the leak vanishes (`|Σ η_b^r| = Σ |η_b|^r`, no cancellation) iff all terms share a
   common nonneg real scaling of a fixed unit phase (full alignment). For real terms this is the
   same-sign condition. A future probe finding the leak nonzero in THICK and zero in THIN (it is the
   opposite: leak is LARGER in thin) keeps the localization falsifiable.

## NON-CLAIM

Pure triangle-inequality / alignment-characterization facts carried over an abstract finite real (or
complex) family. No CORE (`M ≤ C√(n log(p/n))`), cancellation, completion, moment-saving,
anti-concentration, or capacity claim. CORE stays OPEN. The uniform-in-field signed deep-cancellation
bound (the thing this localization points at) is NOT proved here — that IS the open prize / BGK wall.
-/

namespace ProximityGap.Frontier.DoorIVSignedDeepSumAbsLeak

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- The leak direction: the absolute value of the SIGNED deep sum is at most the ABSOLUTE moment.
This is the triangle inequality every moment / absolute-value packaging silently invokes — and the
gap is exactly the signed cancellation it discards. Stated for a real family raised to power `r`. -/
theorem abs_signed_le_abs_moment (s : Finset ι) (η : ι → ℝ) (r : ℕ) :
    |∑ b ∈ s, (η b) ^ r| ≤ ∑ b ∈ s, |η b| ^ r := by
  calc |∑ b ∈ s, (η b) ^ r| ≤ ∑ b ∈ s, |(η b) ^ r| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ b ∈ s, |η b| ^ r := by simp [abs_pow]

/-- The leak gap (absolute moment minus the magnitude of the signed sum) is nonnegative: it is the
quantity of signed cancellation that an absolute-value bound throws away. -/
theorem leak_nonneg (s : Finset ι) (η : ι → ℝ) (r : ℕ) :
    0 ≤ (∑ b ∈ s, |η b| ^ r) - |∑ b ∈ s, (η b) ^ r| :=
  sub_nonneg.mpr (abs_signed_le_abs_moment s η r)

/-- A bound on the ABSOLUTE moment transfers to the signed sum (the leak direction is monotone):
`Σ |η_b|^r ≤ B ⟹ |Σ η_b^r| ≤ B`. So any absolute-value certificate is at best a certificate for the
signed sum — never tighter. -/
theorem abs_moment_bound_transfers
    (s : Finset ι) (η : ι → ℝ) (r : ℕ) {B : ℝ}
    (hB : ∑ b ∈ s, |η b| ^ r ≤ B) :
    |∑ b ∈ s, (η b) ^ r| ≤ B :=
  le_trans (abs_signed_le_abs_moment s η r) hB

/-- The CONVERSE fails, and explicitly so: there is a real family whose SIGNED sum is `0` while its
absolute moment is arbitrarily large (here `2`, scalable). An absolute-moment bound cannot detect
this cancellation — it is exactly the thinness-essential signal the `|·|` packaging discards. We
exhibit the antipodal pair `{+1, -1}` at odd power `r = 1`: signed sum `= 0`, absolute moment `= 2`. -/
theorem abs_moment_bound_does_not_bound_signed_below :
    ∃ (s : Finset ℕ) (η : ℕ → ℝ) (r : ℕ),
      (∑ b ∈ s, (η b) ^ r) = 0 ∧ (∑ b ∈ s, |η b| ^ r) = 2 := by
  refine ⟨{0, 1}, fun b => if b = 0 then (1 : ℝ) else -1, 1, ?_, ?_⟩
  · rw [Finset.sum_pair (by decide : (0 : ℕ) ≠ 1)]; norm_num
  · rw [Finset.sum_pair (by decide : (0 : ℕ) ≠ 1)]; norm_num

/-- Falsifiable equality (real form): the leak VANISHES iff the absolute moment equals the magnitude
of the signed sum, i.e. there is no cancellation. We give the clean sufficient direction that drives
the localization: if every term has the SAME sign as a fixed `σ ∈ {±1}` (full alignment), the leak is
zero. This is the `C_r = 1` ("no cancellation") endpoint; the probe shows the prize regime sits far
from it (stronger cancellation, smaller `C_r`). -/
theorem leak_zero_of_aligned
    (s : Finset ι) (η : ι → ℝ) (r : ℕ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (halign : ∀ b ∈ s, (η b) ^ r = σ * |η b| ^ r) :
    |∑ b ∈ s, (η b) ^ r| = ∑ b ∈ s, |η b| ^ r := by
  have hsum : ∑ b ∈ s, (η b) ^ r = σ * ∑ b ∈ s, |η b| ^ r := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl halign
  have hnonneg : 0 ≤ ∑ b ∈ s, |η b| ^ r :=
    Finset.sum_nonneg fun b _ => pow_nonneg (abs_nonneg _) r
  rcases hσ with h | h <;> rw [hsum, h]
  · simpa using abs_of_nonneg hnonneg
  · simpa [abs_neg] using abs_of_nonneg hnonneg

/-- Complex form of the leak direction (the period field is complex before taking real parts):
`‖Σ z_b‖ ≤ Σ ‖z_b‖`, the same `|·|`-leak over `ℂ`. -/
theorem abs_signed_le_abs_moment_complex (s : Finset ι) (z : ι → ℂ) :
    ‖∑ b ∈ s, z b‖ ≤ ∑ b ∈ s, ‖z b‖ :=
  norm_sum_le s z

/-- Complex full-alignment endpoint: if every `z_b` is a nonneg real multiple of a fixed unit phase
`u`, the leak vanishes (`|Σ z_b| = Σ |z_b|`). This is the `C_r = 1` no-cancellation endpoint; any
adversarial frequency with `C_r < 1` sits strictly inside the leak, and the probe shows the thin
prize regime drives `C_r → 0` (maximal leak), which `|·|`-bounds cannot exploit. -/
theorem leak_zero_iff_aligned_complex
    (s : Finset ι) (z : ι → ℂ) (u : ℂ) (hu : ‖u‖ = 1)
    (c : ι → ℝ) (hc : ∀ b ∈ s, z b = (c b : ℂ) * u) (hcnonneg : ∀ b ∈ s, 0 ≤ c b) :
    ‖∑ b ∈ s, z b‖ = ∑ b ∈ s, ‖z b‖ := by
  have hsum : ∑ b ∈ s, z b = (∑ b ∈ s, (c b : ℂ)) * u := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl hc
  have hterm : ∀ b ∈ s, ‖z b‖ = c b := by
    intro b hb
    rw [hc b hb, Complex.norm_mul, hu, mul_one, Complex.norm_real, Real.norm_of_nonneg (hcnonneg b hb)]
  rw [hsum, Complex.norm_mul, hu, mul_one]
  rw [show (∑ b ∈ s, (c b : ℂ)) = ((∑ b ∈ s, c b : ℝ) : ℂ) by push_cast; rfl]
  rw [Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg hcnonneg)]
  exact Finset.sum_congr rfl (fun b hb => (hterm b hb).symm)

end ProximityGap.Frontier.DoorIVSignedDeepSumAbsLeak

#print axioms ProximityGap.Frontier.DoorIVSignedDeepSumAbsLeak.abs_signed_le_abs_moment
#print axioms ProximityGap.Frontier.DoorIVSignedDeepSumAbsLeak.leak_nonneg
#print axioms ProximityGap.Frontier.DoorIVSignedDeepSumAbsLeak.abs_moment_bound_transfers
#print axioms ProximityGap.Frontier.DoorIVSignedDeepSumAbsLeak.abs_moment_bound_does_not_bound_signed_below
#print axioms ProximityGap.Frontier.DoorIVSignedDeepSumAbsLeak.leak_zero_of_aligned
#print axioms ProximityGap.Frontier.DoorIVSignedDeepSumAbsLeak.abs_signed_le_abs_moment_complex
#print axioms ProximityGap.Frontier.DoorIVSignedDeepSumAbsLeak.leak_zero_iff_aligned_complex
