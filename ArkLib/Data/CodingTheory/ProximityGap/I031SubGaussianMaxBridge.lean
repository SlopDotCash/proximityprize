/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumOrbitReduction

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# I031 Step (b)-(iv): the sub-Gaussian max bridge — `max ≤ √(2C·log m)` (#444 / #389)

This is the **L7-style modular packaging** of the I031 handle on the Proximity-Prize δ* core.
The prize sup-norm is `M(μ_n) = max_{b≠0} ‖η_b‖`, `η_b = Σ_{x∈μ_n} ψ(b·x)`, with target
`M ≤ C·√(n·log(p/n))`. The campaign reduced the whole bound to a *single* analytic input:

* **Orbit reduction** (`SubgroupGaussSumOrbitReduction.card_distinct_eta_le`): `η` is
  orbit-invariant (`η_{ζb} = η_b` for `ζ ∈ G`), so there are at most `m = [F^*:G] (+1)`
  **distinct** periods, indexed by a transversal of `F^*/G`.
* **Flat chaining metric** (`I031MatchedGaussianCovariance.matchedCov_l2_average`): the matched
  Gaussian covariance averages to `n`, the chaining metric is FLAT, so generic chaining
  collapses to the **union bound over the `m` periods** — chaining/geometry add nothing.

So the entire I031 bound is the standard *"max of `m` sub-Gaussian-tailed values is
`≤ √(2C·n·log m)"`* union argument, **conditional on one named open Prop** — the per-period
sub-Gaussian tail of the cyclotomic Gauss period at depth (= the recognized-open BGK/Lamzouri
short-character-sum wall; equivalently the Paley-graph-conjecture face of the open core, see the
δ* programme guide §3.5 face 3).

## What this file delivers (axiom-clean)

1. `SubGaussianTailBound S C m : Prop` — the open input in its cleanest formalizable form: the
   level-set count of a finset `S ⊆ ℝ` of magnitudes is `≤ m·exp(−s²/2C)` for every threshold
   `s > 0`. The consumer applies it with `S =` the period magnitudes and proxy `C = C₀·n`.
2. `subgaussian_max_le` — **the CONDITIONAL BRIDGE (PROVEN, axiom-clean)**:
   `SubGaussianTailBound S C m → 1 ≤ m → 0 < C → ∀ v ∈ S, v ≤ √(2·C·log m)`.
   At the threshold `s* = √(2C·log m)` the tail gives count `≤ m·exp(−log m) = 1`; pushing `s` a
   hair past `s*` drives the count strictly below `1` (hence to `0` as a `ℕ`), so no `v` can
   exceed `s*` — a clean contrapositive, no `ε`-fudge needed.
3. `periodMagnitudes` + `norm_eta_mem_periodMagnitudes` + `i031_norm_eta_le_of_subGaussian` —
   the wiring to the period family: specializing `S` to the magnitudes `{‖η_b‖}` and `C = C₀·n`
   yields `‖η_b‖ ≤ √(2·C₀·n·log m)` for *every* `b`, **conditional on**
   `SubGaussianTailBound (periodMagnitudes ψ G) (C₀·n) m`. Combined with `card_distinct_eta_le`
   (`m =` transversal size) this is the I031 union bound `M(μ_n) ≤ √(2·C₀·n·log m)`.

## Honest scope

The conditional bridge (2) and its period specialization (3) are PROVEN axiom-clean. The
hypothesis `SubGaussianTailBound (periodMagnitudes ψ G) (C₀·n) m` is the SINGLE recognized-open
analytic input — the per-period sub-Gaussian tail of the cyclotomic Gauss period at depth, the
BGK/Lamzouri wall. **NO closure is claimed.** This round established that chaining and geometry
add nothing beyond this union bound (`I031MatchedGaussianCovariance`), so this file is the
reusable conditional brick that consumes exactly that one Prop.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
-/

open Finset AddChar

namespace ArkLib.ProximityGap.I031SubGaussianMaxBridge

/-! ## 1. The named open input -/

/-- **The sub-Gaussian tail bound (the single open input).** A finset `S ⊆ ℝ` of magnitudes
satisfies `SubGaussianTailBound S C m` when, for every threshold `s > 0`, the number of members
exceeding `s` is at most `m·exp(−s²/(2C))`. For the I031 consumer, `S` is the set of period
magnitudes `{‖η_b‖}`, `m` is the number of distinct periods (orbit-count `[F^*:G]+1`), and the
proxy variance is `C = C₀·n` (the proven √n average scale). This is the recognized-open
per-period sub-Gaussian tail — the BGK/Lamzouri short-character-sum wall. -/
def SubGaussianTailBound (S : Finset ℝ) (C m : ℝ) : Prop :=
  ∀ s : ℝ, 0 < s → ((S.filter (fun v => s < v)).card : ℝ) ≤ m * Real.exp (-(s ^ 2) / (2 * C))

/-! ## 1a. Exact falsification certificate for the named input -/

/-- **Exact failure certificate for `SubGaussianTailBound`.** The full sub-Gaussian tail input
fails if and only if there is a concrete positive threshold `s` whose empirical tail count beats
the Gaussian envelope `m·exp(-s²/(2C))`.

This is the scanner-facing form of the BGK/Lamzouri wall: a counterexample to the named input is
not an amorphous negation, but a threshold/count certificate. -/
theorem not_SubGaussianTailBound_iff_exists_tail_count_gt
    (S : Finset ℝ) (C m : ℝ) :
    (¬ SubGaussianTailBound S C m) ↔
      ∃ s : ℝ, 0 < s ∧
        m * Real.exp (-(s ^ 2) / (2 * C)) < ((S.filter (fun v => s < v)).card : ℝ) := by
  constructor
  · intro hfail
    by_contra hnone
    apply hfail
    intro s hs
    exact le_of_not_gt (fun hgt => hnone ⟨s, hs, hgt⟩)
  · rintro ⟨s, hs, hgt⟩ htail
    exact not_lt_of_ge (htail s hs) hgt

/-! ## 2. The conditional bridge (proven, axiom-clean) -/

/-- **The conditional sub-Gaussian max bridge.** From the tail bound, with `0 < C` and `1 ≤ m`,
every magnitude `v ∈ S` satisfies `v ≤ √(2·C·log m)`. Hence the maximum of the finset is bounded
by `√(2·C·log m)` — exactly the union bound over `m` sub-Gaussian-tailed values.

*Proof.* By contradiction: if some `v ∈ S` exceeds `s* := √(2·C·log m)`, pick `s` strictly
between `s*` and `v`. Then `s² > (s*)² = 2C·log m`, so `−s²/(2C) < −log m`, hence
`m·exp(−s²/(2C)) < m·exp(−log m) = m·m⁻¹ = 1`. The tail bound forces the count of members `> s`
to be `< 1`, i.e. `0` as a `ℕ`; but `v > s` makes `v` such a member, so the count is `≥ 1` —
contradiction. The strict push past `s*` is what cleanly handles the `≤ 1` boundary. -/
theorem subgaussian_max_le
    {S : Finset ℝ} {C m : ℝ} (hC : 0 < C) (hm : 1 ≤ m)
    (h : SubGaussianTailBound S C m) :
    ∀ v ∈ S, v ≤ Real.sqrt (2 * C * Real.log m) := by
  intro v hv
  by_contra hlt
  rw [not_le] at hlt
  set sstar := Real.sqrt (2 * C * Real.log m) with hsstar
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm
  have h2C : 0 < 2 * C := by linarith
  have hrad : 0 ≤ 2 * C * Real.log m := by positivity
  have hsstar_nonneg : 0 ≤ sstar := Real.sqrt_nonneg _
  set s := (sstar + v) / 2 with hs
  have hs_lo : sstar < s := by rw [hs]; linarith
  have hs_hi : s < v := by rw [hs]; linarith
  have hs_pos : 0 < s := lt_of_le_of_lt hsstar_nonneg hs_lo
  have hsstar_sq : sstar ^ 2 = 2 * C * Real.log m := by
    rw [hsstar, Real.sq_sqrt hrad]
  have hs_sq_gt : 2 * C * Real.log m < s ^ 2 := by
    rw [← hsstar_sq]
    nlinarith [hsstar_nonneg, hs_lo, sq_nonneg (s - sstar)]
  have hexp_arg : -(s ^ 2) / (2 * C) < -Real.log m := by
    rw [div_lt_iff₀ h2C]
    nlinarith [hs_sq_gt, h2C]
  have hexp_lt : Real.exp (-(s ^ 2) / (2 * C)) < Real.exp (-Real.log m) :=
    Real.exp_lt_exp.mpr hexp_arg
  have hm_pos : 0 < m := lt_of_lt_of_le one_pos hm
  have hexp_neglog : Real.exp (-Real.log m) = m⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hm_pos]
  have hbound : m * Real.exp (-(s ^ 2) / (2 * C)) < 1 := by
    have hh : m * Real.exp (-(s ^ 2) / (2 * C)) < m * Real.exp (-Real.log m) :=
      mul_lt_mul_of_pos_left hexp_lt hm_pos
    rw [hexp_neglog, mul_inv_cancel₀ (ne_of_gt hm_pos)] at hh
    exact hh
  have htail := h s hs_pos
  have hcard_lt : ((S.filter (fun w => s < w)).card : ℝ) < 1 := lt_of_le_of_lt htail hbound
  have hv_mem : v ∈ S.filter (fun w => s < w) := by
    rw [Finset.mem_filter]; exact ⟨hv, hs_hi⟩
  have hcard_pos : 1 ≤ (S.filter (fun w => s < w)).card := Finset.card_pos.mpr ⟨v, hv_mem⟩
  have hc1 : (1 : ℝ) ≤ ((S.filter (fun w => s < w)).card : ℝ) := by exact_mod_cast hcard_pos
  linarith

/-! ## 3. Wiring to the Gauss-period family -/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The finset of period magnitudes** `{‖η_b‖ : b ∈ F}` (the distinct values of `b ↦ ‖η_b‖`).
This is the `S` the bridge consumes. By orbit invariance there are at most `m = [F^*:G]+1`
distinct *periods* (`SubgroupGaussSumOrbitReduction.card_distinct_eta_le`), hence at most `m`
distinct magnitudes; `m` is the union-bound count. -/
noncomputable def periodMagnitudes (ψ : AddChar F ℂ) (G : Finset F) : Finset ℝ :=
  (Finset.univ.image (eta ψ G)).image (fun z => ‖z‖)

/-- Period-specialized failure certificate for the named sub-Gaussian input. To refute the
period tail assumption it is enough, and necessary, to exhibit a threshold whose period-magnitude
tail count exceeds the Gaussian envelope. -/
theorem not_periodSubGaussianTailBound_iff_exists_tail_count_gt
    (ψ : AddChar F ℂ) (G : Finset F) (C m : ℝ) :
    (¬ SubGaussianTailBound (periodMagnitudes ψ G) C m) ↔
      ∃ s : ℝ, 0 < s ∧
        m * Real.exp (-(s ^ 2) / (2 * C)) <
          (((periodMagnitudes ψ G).filter (fun v => s < v)).card : ℝ) := by
  simpa using
    (not_SubGaussianTailBound_iff_exists_tail_count_gt
      (S := periodMagnitudes ψ G) (C := C) (m := m))

/-- Every period magnitude `‖η_b‖` lies in `periodMagnitudes`. -/
theorem norm_eta_mem_periodMagnitudes (ψ : AddChar F ℂ) (G : Finset F) (b : F) :
    ‖eta ψ G b‖ ∈ periodMagnitudes ψ G := by
  unfold periodMagnitudes
  rw [Finset.mem_image]
  exact ⟨eta ψ G b, Finset.mem_image_of_mem _ (Finset.mem_univ b), rfl⟩

/-- **The I031 union bound (conditional on the named open input).** With proxy variance `C₀·n`
(`0 < C₀·n`) and orbit-count `m ≥ 1`, if the period magnitudes satisfy the sub-Gaussian tail
bound, then **every** period magnitude is `≤ √(2·C₀·n·log m)`:

> `M(μ_n) = max_{b} ‖η_b‖ ≤ √(2·C₀·n·log m)`.

This is the L7-modular I031 deliverable: the bound is PROVEN axiom-clean *given* the single open
analytic Prop `SubGaussianTailBound (periodMagnitudes ψ G) (C₀·n) m`. NO closure is claimed; that
Prop is the BGK/Lamzouri per-period tail wall. -/
theorem i031_norm_eta_le_of_subGaussian (ψ : AddChar F ℂ) (G : Finset F) {C₀ n m : ℝ}
    (hC : 0 < C₀ * n) (hm : 1 ≤ m)
    (h : SubGaussianTailBound (periodMagnitudes ψ G) (C₀ * n) m) (b : F) :
    ‖eta ψ G b‖ ≤ Real.sqrt (2 * (C₀ * n) * Real.log m) :=
  subgaussian_max_le hC hm h _ (norm_eta_mem_periodMagnitudes ψ G b)

end ArkLib.ProximityGap.I031SubGaussianMaxBridge

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.I031SubGaussianMaxBridge.not_SubGaussianTailBound_iff_exists_tail_count_gt
#print axioms ArkLib.ProximityGap.I031SubGaussianMaxBridge.subgaussian_max_le
#print axioms ArkLib.ProximityGap.I031SubGaussianMaxBridge.not_periodSubGaussianTailBound_iff_exists_tail_count_gt
#print axioms ArkLib.ProximityGap.I031SubGaussianMaxBridge.norm_eta_mem_periodMagnitudes
#print axioms ArkLib.ProximityGap.I031SubGaussianMaxBridge.i031_norm_eta_le_of_subGaussian
