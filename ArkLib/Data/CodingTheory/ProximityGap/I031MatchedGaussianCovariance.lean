/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
metric is FLAT: `d(b,b') ≈ √(2|G|)` for almost every distinct pair, with the fraction of close pairs
`→ 0` as `|G|` grows. What is proved here is only the **L²-average of the covariance over difference
frequencies**: by the second moment `Σ_c ‖η_c‖² = q|G|`, the average of `‖η_c‖²` over all `q`
frequencies `c` is exactly `|G|`, so the **root-mean-square** covariance is `√|G|`. This L²
information does not by itself say that a *typical* covariance has size `√|G|`, that the typical
squared metric is `2|G|`, or that close pairs are a vanishing fraction (compare audit finding
PG-048); those remain probe observations.

**No quotient / index reduction for the Gaussian process (audit finding PG-148).** The deterministic
periods are constant on multiplicative cosets (`η_{hb} = η_b` for `h ∈ G`), but the matched Gaussian
process `G_b = Σ_{x∈G} g_x ψ(b·x)` does **not** inherit this samplewise: dilation `b ↦ hb` permutes
the iid coefficients `g_x`, which preserves the joint law but does not identify `G_b` with `G_{hb}`.
Correspondingly the metric is built from `η_{b−b'}`, not from `η_b − η_{b'}`, and it does not
descend to the coset quotient. Example: `G = {1, −1} ⊆ F₅`, `ψ(t) = exp(2πit/5)`; the frequencies
`1` and `4` lie in one coset and `η_1 = η_4`, yet `d(1,4)² = 4 − 4cos(4π/5) > 0`. So a union
bound over only `m = (q−1)/|G|` Gaussian indices cannot be inferred from the deterministic coset
invariance; a comparison must either keep the full Gaussian index set or state a
representative-indexed comparison and prove the domination it needs, which is not done here.
(The Salem–Zygmund discussion in
`docs/kb/deltastar-salem-zygmund-gausssum-chaining-2026-06-13.md` is background, not a
consequence of this file.)

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
exactly `|G|`, i.e. the root-mean-square covariance is `√|G|`. This is L² information only: it does
not prove that a typical covariance has that size or that close pairs are rare, and it does not
justify reducing the Gaussian index set from `q` frequencies to `m = (q−1)/|G|` cosets (the matched
metric does not descend to the coset quotient; see the module docstring). No Weil. -/
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
