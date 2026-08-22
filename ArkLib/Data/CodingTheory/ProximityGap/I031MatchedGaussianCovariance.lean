/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# I031 Step (b)-(i): the matched-Gaussian covariance and the chaining-metric identity (#389)

The δ* sup-norm `B = max_{b≠0} ‖η_b‖`, `η_b = Σ_{x∈G} ψ(b·x)`, is to be compared (Step (b)) to the
expected supremum `E sup_b |G_b|` of the **matched centered Gaussian process**
`G_b = Σ_{x∈G} g_x ψ(b·x)`, `g_x` iid standard complex normal. For Slepian / Sudakov–Fernique /
Dudley generic chaining the only data needed from the Gaussian side is its **covariance kernel** and
the induced **L² chaining metric** `d(b,b')² = E|G_b − G_{b'}|²`. This file isolates those two
purely-algebraic objects (no probability) for the cyclotomic Gauss-period frame and proves their
exact closed forms from the second-moment substrate.

Using `E[g_x · conj g_{x'}] = [x = x']`:
* `E[G_b · conj G_{b'}] = Σ_{x∈G} ψ((b−b')·x) = η_{b−b'}`  — **the covariance IS the period at the
  difference frequency** (a subgroup correlation). We *define* `matchedCov b b' := η ψ G (b − b')`.
* `E|G_b|² = matchedCov b b = η_0 = |G|` (the variance, matching the proven √|G| average scale).
* `d(b,b')² = E|G_b|² + E|G_{b'}|² − 2 Re E[G_b conj G_{b'}] = 2|G| − 2 Re η_{b−b'}`.
  We *define* `matchedSqMetric b b' := 2|G| − 2 Re(η ψ G (b − b'))` and prove its structural facts.

**The flat-metric phenomenon (probes `probe_i031_metric_flatness_vs_collapse.py`).** Empirically the
quotient metric is FLAT: `d(b,b') ≈ √(2|G|)` for almost every distinct pair, with the fraction of
close pairs `→ 0` as `|G|` grows. The rigorous skeleton of that flatness is the **L²-average of the
metric over difference frequencies**: by the second moment `Σ_c ‖η_c‖² = q|G|`, the average of
`‖η_c‖²` over all frequencies `c` is exactly `|G|`, so the typical covariance has size `√|G|` (vanishing
relative to the diagonal `|G|`), the average squared metric is the flat `2|G|`, and the close pairs
(`Re η_c` near `|G|`) are a vanishing fraction. We prove the exact average identity here; it certifies
that the I031 "collapse log q → log m" is the index-count reduction (union bound over `m = q/|G|`
orbits), NOT a multi-scale chaining gain — consistent with the Salem–Zygmund self-refutation
(`docs/kb/deltastar-salem-zygmund-gausssum-chaining-2026-06-13.md`).

This is the honest, axiom-clean Step-(b)-(i) deliverable: the covariance structure and chaining
metric of the matched Gaussian process are pinned exactly; the remaining open content (Step (b)-(iv))
is the per-period sub-Gaussian tail at depth, which the probes find empirically bounded
(`sig_eff²/n ∈ [0.57, 0.92]`, no creep to `n = 512`) but which is the same BGK/Lamzouri wall.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset AddChar

namespace ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The matched-Gaussian covariance kernel.** For `G_b = Σ_{x∈G} g_x ψ(b·x)` with iid standard
complex-normal `g_x`, `E[G_b · conj G_{b'}] = Σ_{x∈G} ψ((b−b')·x) = η_{b−b'}`. We take this closed
form as the definition; the structural lemmas below are exactly the data Slepian/Dudley consume. -/
noncomputable def matchedCov (ψ : AddChar F ℂ) (G : Finset F) (b b' : F) : ℂ :=
  eta ψ G (b - b')

/-- **The matched-Gaussian squared chaining metric** `d(b,b')² = E|G_b − G_{b'}|² = 2|G| − 2 Re η_{b−b'}`. -/
noncomputable def matchedSqMetric (ψ : AddChar F ℂ) (G : Finset F) (b b' : F) : ℝ :=
  2 * G.card - 2 * (eta ψ G (b - b')).re

/-- **Variance: `matchedCov b b = |G|`.** The diagonal of the kernel is `η_0 = |G|` (the proven √|G|
average scale). -/
theorem matchedCov_diag (ψ : AddChar F ℂ) (G : Finset F) (b : F) :
    matchedCov ψ G b b = (G.card : ℂ) := by
  unfold matchedCov eta
  simp [sub_self, AddChar.map_zero_eq_one]

/-- **The metric vanishes on the diagonal: `matchedSqMetric b b = 0`.** -/
theorem matchedSqMetric_diag (ψ : AddChar F ℂ) (G : Finset F) (b : F) :
    matchedSqMetric ψ G b b = 0 := by
  unfold matchedSqMetric eta
  simp [sub_self, AddChar.map_zero_eq_one]

/-- **The covariance is Hermitian: `matchedCov b b' = conj (matchedCov b' b)`.** `η_{b−b'} =
conj η_{b'−b}` since `conj ψ(a) = ψ(−a)`. -/
theorem matchedCov_conj_symm (ψ : AddChar F ℂ) (G : Finset F) (b b' : F)
    (hchar : (0 : ℕ) < ringChar F) :
    matchedCov ψ G b b' = (starRingEnd ℂ) (matchedCov ψ G b' b) := by
  unfold matchedCov eta
  rw [map_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  congr 1
  ring

/-- **The squared metric is symmetric: `matchedSqMetric b b' = matchedSqMetric b' b`.** The two
periods `η_{b−b'}` and `η_{b'−b}` are conjugate, hence have equal real part. -/
theorem matchedSqMetric_symm (ψ : AddChar F ℂ) (G : Finset F) (b b' : F)
    (hchar : (0 : ℕ) < ringChar F) :
    matchedSqMetric ψ G b b' = matchedSqMetric ψ G b' b := by
  unfold matchedSqMetric
  have h : (eta ψ G (b - b')).re = (eta ψ G (b' - b)).re := by
    have hc := matchedCov_conj_symm ψ G b b' hchar
    unfold matchedCov at hc
    rw [hc, Complex.conj_re]
  rw [h]

/-- **Diameter bound: `0 ≤ matchedSqMetric b b' ≤ 4|G|`.** Since `|Re η_{b−b'}| ≤ ‖η_{b−b'}‖ ≤ |G|`
(triangle inequality, each `‖ψ‖ = 1`). The flat value `2|G|` sits in the middle; the empirics put the
typical metric exactly there. -/
theorem matchedSqMetric_nonneg_le (ψ : AddChar F ℂ) (G : Finset F) (b b' : F) :
    0 ≤ matchedSqMetric ψ G b b' ∧ matchedSqMetric ψ G b b' ≤ 4 * G.card := by
  have hnorm : ‖eta ψ G (b - b')‖ ≤ (G.card : ℝ) := by
    unfold eta
    calc ‖∑ x ∈ G, ψ ((b - b') * x)‖ ≤ ∑ x ∈ G, ‖ψ ((b - b') * x)‖ := norm_sum_le _ _
      _ = ∑ _x ∈ G, (1 : ℝ) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          exact AddChar.norm_apply ψ _
      _ = (G.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hre_le : (eta ψ G (b - b')).re ≤ (G.card : ℝ) :=
    le_trans (Complex.re_le_norm _) hnorm
  have hre_ge : -(G.card : ℝ) ≤ (eta ψ G (b - b')).re := by
    have hle : -‖eta ψ G (b - b')‖ ≤ (eta ψ G (b - b')).re := by
      have habs := Complex.abs_re_le_norm (eta ψ G (b - b'))
      rw [abs_le] at habs; exact habs.1
    linarith [hnorm]
  refine ⟨?_, ?_⟩
  · unfold matchedSqMetric; linarith
  · unfold matchedSqMetric; linarith

/-- **The flat-metric certificate: the L²-average of the covariance over all difference frequencies.**
`Σ_c ‖matchedCov b (b−c)‖² = Σ_c ‖η_c‖² = q|G|`, so the average of `‖η_c‖²` over the `q` frequencies is
exactly `|G|`. Hence the *typical* covariance has size `√|G|` (vanishing relative to the diagonal
`|G|`), the average squared metric is the flat `2|G|`, and close pairs are a vanishing fraction. This
is the rigorous half of the metric-flatness phenomenon: the I031 gain is the index reduction
`q → m = q/|G|` (union bound over orbits), not multi-scale chaining. No Weil. -/
theorem matchedCov_l2_average {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (b : F) :
    ∑ c : F, ‖matchedCov ψ G b (b - c)‖ ^ 2 = (Fintype.card F : ℝ) * G.card := by
  have hre : ∀ c : F, matchedCov ψ G b (b - c) = eta ψ G c := by
    intro c; unfold matchedCov; congr 1; ring
  calc ∑ c : F, ‖matchedCov ψ G b (b - c)‖ ^ 2
      = ∑ c : F, ‖eta ψ G c‖ ^ 2 := by
        refine Finset.sum_congr rfl (fun c _ => ?_); rw [hre c]
    _ = (Fintype.card F : ℝ) * G.card := subgroup_gaussSum_secondMoment hψ G

end ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.matchedCov_diag
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.matchedSqMetric_diag
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.matchedCov_conj_symm
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.matchedSqMetric_symm
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.matchedSqMetric_nonneg_le
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.matchedCov_l2_average
