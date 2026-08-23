/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodCosetReduction
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodOptimizedBound
import ArkLib.Data.CodingTheory.ProximityGap.InteriorWorstCaseIncompleteSum
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# R376: per-frequency-shadow — the coset-sharpened `⌈log m⌉`-depth sup endpoint (#466)

Session 2026-07-09, issue #466, route `per-frequency-shadow`.  Companion to this session's
r341 exact Mellin/coset dictionary (`_R341CAZACCosetEquivalence.lean`, commit 681128736):
max-Mellin PAPR ⟺ max-coset Gaussian-period bound, so the sup-norm object bounded below IS
the CAZAC/PAPR wall in coset coordinates.

## Dictionary (paper → Lean)

With `q = Fintype.card F`, `G = μ_n ⊆ F^×` a multiplicative subgroup (`n = G.card`, encoded
by `hbij`/`h0`/`hne` as in the landed `GaussPeriodCosetReduction.lean`), `m = (q−1)/n` the
coset count (`hcount : q = n·m + 1`), `η_b = eta ψ G b`, and `E_r = rEnergy G r`:

* the named residual `DCEnergyBoundWithConstant G r K` (restated VERBATIM from
  `Frontier/_R240GeneralRFoldVariance.lean` — frontier files must not import frontier files;
  a consumer importing both files can weld the two statements by `Iff.rfl`) is the
  DC-subtracted depth-`r` Wick bound `q·E_r − n^{2r} ≤ q·K^r·(2r−1)!!·n^r`;
* `sup_{b≠0} ‖η_b‖` is the non-principal spectral radius of the generalized Paley graph
  `Cay(F_q, μ_n)`, and the in-tree named open Prop `WorstCaseIncompleteSumBound ψ G M`
  (`InteriorWorstCaseIncompleteSum.lean`) states `‖η_b‖² ≤ M` for all `b ≠ 0`.

## PROVEN here (machine-checked, axiom-clean)

* `coset_eta_pow_le_of_dcEnergyBoundWithConstant` — coset-granular per-frequency moment
  bound: the residual at depth `r` gives `‖η_b‖^{2r} ≤ (q/n)·K^r·(2r−1)!!·n^r` for `b ≠ 0`.
  The `/n` is the orbit multiplicity `η_{ub} = η_b` (`u ∈ G`) via the landed
  `card_mul_eta_pow_le_sum_erase`; it is exactly the `n`-fold sharpening that the crude
  all-`b` `single_le_sum` route (R240's `eta_pow_le_of_dcEnergyBoundWithConstant`) discards.
* `eta_sq_le_cosetOptimizedWithConstant` — optimized square bound at coset depth: for any
  real majorant `q ≤ n·μ` and any depth `r ≥ log μ`, `‖η_b‖² ≤ 2e·K·n·r`.  **`log m`
  replaces `log q`** relative to the in-tree `⌈log q⌉`-depth consumer chain
  (`eta_sq_le_dcOptimizedWithConstant` / `DCEnergyCeilWallWithConstant` in R240), removing
  that route's `√(log q / log m)` loss.  At the prize shape (`n = 2^30`, `m ≈ 2^128`,
  `q ≈ n·m`) the operative depth drops from `⌈ln q⌉ = 110` to `⌈ln(m+1)⌉ = 89`.
* `worstCase_of_dcEnergyBoundWithConstant_logDepth` and
  `worstCase_of_dcEnergyBoundWithConstant_cosetCount` — the endpoint: ONE rung of the
  residual, at depth `k₀ = ⌈log(m+1)⌉`, yields the in-tree named target
  `WorstCaseIncompleteSumBound ψ G (2e·K·n·(log(m+1)+1))`, i.e.
  `sup_{b≠0}‖η_b‖ ≤ √(2e·K·n·(log(m+1)+1))` — the per-frequency shadow at scale
  `√(C·n·log m)`, stronger than the prize-window `√(C·n·log p)` form since `m < p`.
* `card_mul_eta_pow_le_dcGap` — the UNCONDITIONAL converse floor
  `n·‖η_{b₀}‖^{2r} ≤ q·E_r − n^{2r}` for every `b₀ ≠ 0` and every depth `r`: the
  DC-subtracted energy is bounded BELOW by the sup norm at coset granularity.
* `not_dcEnergyBoundWithConstant_of_eta_gt` — converse consumer: a single per-frequency
  value above the matched scale refutes the residual at the same `(r, K)`.  Together with
  the forward direction this machine-checks the "no free lunch" faithfulness of the
  depth-`⌈log m⌉` moment route: the residual is not a weaker surrogate.  (The quantitative
  two-sided sandwich constant is a paper computation — factor `e` in `R²`, NOT `2`; the
  factor-2 claim was a verifier-corrected normalization artifact.  Only the two
  implications, not the constant-`e` sandwich, are formalized here.)

## NAMED OPEN (do not discharge)

* `DCEnergyBoundWithConstant G k₀ K` at `k₀ = ⌈log(m+1)⌉` with `K = O(1)` — equivalently
  the depth-`k₀` additive-energy bound on `N_{k₀}(μ_n)`.  By the converse above it is
  equivalent (within an absolute constant) to the sup-norm bound itself: it IS the prize
  wall in energy coordinates.  The honest open window `(log p)^{1+ε} ≤ m ≤ p/(log p)^{1+ε}`
  (r341) is unchanged — this brick re-coordinates the wall; it does not move it.

Everything below is proved; no `sorry`, no new axioms.  The concentration phenomenology
behind this route (top-coset excess shares, κ_eff saturation) is session numerics —
evidence, not proof — and is not consumed anywhere in this file.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodCosetReduction
open ArkLib.ProximityGap.GaussPeriodOptimizedBound
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum

namespace ArkLib.ProximityGap.R376ShadowLogM

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Constant-`K` DC-subtracted depth-`r` Wick target
`q·E_r − n^{2r} ≤ q·K^r·(2r−1)!!·n^r` — the named OPEN residual, restated verbatim from
`Frontier/_R240GeneralRFoldVariance.lean` (`R240GeneralRFoldVariance.DCEnergyBoundWithConstant`;
definitionally identical, weld by `Iff.rfl` in any consumer importing both files).  Do not
discharge: at depth `⌈log m⌉` this is the prize wall in energy coordinates. -/
def DCEnergyBoundWithConstant (G : Finset F) (r : ℕ) (K : ℝ) : Prop :=
  (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
    ≤ (Fintype.card F : ℝ)
        * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))

/-- **Coset-sharpened per-frequency moment bound.**  For a multiplicative subgroup `G`
(`hbij`/`h0`/`hne`), the depth-`r` residual gives, for every nonzero frequency,
`‖η_b‖^{2r} ≤ (q/n)·K^r·(2r−1)!!·n^r`.  The division by `n = G.card` is the coset
reduction (the max is attained on a full `n`-element multiplication orbit); the crude
all-`b` route (R240) has `q` in place of `q/n`. -/
theorem coset_eta_pow_le_of_dcEnergyBoundWithConstant
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun y => u * y) = G) (h0 : (0 : F) ∉ G) (hne : G.Nonempty)
    {r : ℕ} {K : ℝ} (h : DCEnergyBoundWithConstant G r K) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) / (G.card : ℝ)
          * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) := by
  classical
  have hn : (0 : ℝ) < (G.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
  have hmoment : ∑ b' : F, ‖eta ψ G b'‖ ^ (2 * r) = (Fintype.card F : ℝ) * rEnergy G r :=
    subgroup_gaussSum_moment hψ G r
  have heta0 : ‖eta ψ G (0 : F)‖ ^ (2 * r) = (G.card : ℝ) ^ (2 * r) := by
    rw [eta_zero, Complex.norm_natCast]
  have hsum_erase : ∑ b' ∈ Finset.univ.erase (0 : F), ‖eta ψ G b'‖ ^ (2 * r)
      = (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0), hmoment, heta0]
  have hcoset := card_mul_eta_pow_le_sum_erase (ψ := ψ) hbij h0 r hb
  rw [hsum_erase] at hcoset
  unfold DCEnergyBoundWithConstant at h
  have hchain : (G.card : ℝ) * ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ)
          * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) :=
    hcoset.trans h
  rw [div_mul_eq_mul_div, le_div_iff₀ hn]
  exact (mul_comm (‖eta ψ G b‖ ^ (2 * r)) ((G.card : ℝ))).trans_le hchain

/-- **The coset-optimized square bound.**  If `μ` majorizes the coset count (`q ≤ n·μ`) and
the depth satisfies `r ≥ log μ`, then the depth-`r` residual gives `‖η_b‖² ≤ 2e·K·n·r` for
every `b ≠ 0`.  This is the in-tree `eta_sq_le_dcOptimizedWithConstant` with its field-size
collapse `q^{1/r} ≤ e` (needing `r ≥ log q`) replaced by the coset collapse
`(q/n)^{1/r} ≤ μ^{1/r} ≤ e` (needing only `r ≥ log μ ≈ log m`). -/
theorem eta_sq_le_cosetOptimizedWithConstant
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun y => u * y) = G) (h0 : (0 : F) ∉ G) (hne : G.Nonempty)
    {r : ℕ} {K μ : ℝ} (hr : 1 ≤ r)
    (hμ : (Fintype.card F : ℝ) ≤ (G.card : ℝ) * μ) (hrμ : Real.log μ ≤ r) (hK : 0 ≤ K)
    (h : DCEnergyBoundWithConstant G r K) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ 2 ≤ 2 * Real.exp 1 * K * (G.card : ℝ) * (r : ℝ) := by
  have hn : (0 : ℝ) < (G.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hrne : (r : ℕ) ≠ 0 := by omega
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hμpos : 0 < μ := by
    by_contra hcon
    push_neg at hcon
    nlinarith [hqpos.trans_le hμ, hn]
  have hqn_le : (Fintype.card F : ℝ) / (G.card : ℝ) ≤ μ := by
    rw [div_le_iff₀ hn]
    calc (Fintype.card F : ℝ) ≤ (G.card : ℝ) * μ := hμ
      _ = μ * (G.card : ℝ) := by ring
  have hd0 : (0 : ℝ) ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) := by positivity
  have hWnn : (0 : ℝ)
      ≤ K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by positivity
  have hpow : (‖eta ψ G b‖ ^ 2) ^ r
      ≤ μ * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) := by
    rw [← pow_mul]
    exact (coset_eta_pow_le_of_dcEnergyBoundWithConstant hψ hbij h0 hne h hb).trans
      (mul_le_mul_of_nonneg_right hqn_le hWnn)
  have hstep1 : ‖eta ψ G b‖ ^ 2
      ≤ (μ * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)))
          ^ ((r : ℝ)⁻¹) := by
    calc ‖eta ψ G b‖ ^ 2
        = ((‖eta ψ G b‖ ^ 2) ^ r) ^ ((r : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast (sq_nonneg _) hrne).symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hpow (by positivity)
  have hexpand :
      (μ * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)))
          ^ ((r : ℝ)⁻¹)
        = μ ^ ((r : ℝ)⁻¹) * K
            * (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹) * (G.card : ℝ) := by
    rw [Real.mul_rpow (le_of_lt hμpos) (by positivity : (0 : ℝ) ≤ K ^ r
        * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)),
      Real.mul_rpow (by positivity : (0 : ℝ) ≤ K ^ r)
        (mul_nonneg hd0 (by positivity : (0 : ℝ) ≤ (G.card : ℝ) ^ r)),
      Real.mul_rpow hd0 (by positivity : (0 : ℝ) ≤ (G.card : ℝ) ^ r),
      Real.pow_rpow_inv_natCast hK hrne,
      Real.pow_rpow_inv_natCast (by positivity : (0 : ℝ) ≤ (G.card : ℝ)) hrne]
    ring
  rw [hexpand] at hstep1
  have hbq : μ ^ ((r : ℝ)⁻¹) ≤ Real.exp 1 := rpow_inv_le_exp_one hμpos hr0 hrμ
  have hbd : (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹) ≤ 2 * (r : ℝ) := by
    calc (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹)
        ≤ (((2 * r : ℕ) : ℝ) ^ r) ^ ((r : ℝ)⁻¹) :=
          Real.rpow_le_rpow hd0 (doubleFactorial_le_pow r) (by positivity)
      _ = ((2 * r : ℕ) : ℝ) := Real.pow_rpow_inv_natCast (by positivity) hrne
      _ = 2 * (r : ℝ) := by push_cast; ring
  calc ‖eta ψ G b‖ ^ 2
      ≤ μ ^ ((r : ℝ)⁻¹) * K
          * (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹) * (G.card : ℝ) := hstep1
    _ ≤ Real.exp 1 * K * (2 * (r : ℝ)) * (G.card : ℝ) := by gcongr
    _ = 2 * Real.exp 1 * K * (G.card : ℝ) * (r : ℝ) := by ring

/-- **The `⌈log μ⌉`-depth endpoint.**  ONE rung of the residual, at the coset-optimal depth
`⌈log μ⌉` (any majorant `q ≤ n·μ`, `μ ≥ e`), delivers the in-tree named per-frequency
target `WorstCaseIncompleteSumBound` at scale `M = 2e·K·n·(log μ + 1)`, i.e.
`sup_{b≠0}‖η_b‖ ≤ √(2e·K·n·(log μ + 1))`. -/
theorem worstCase_of_dcEnergyBoundWithConstant_logDepth
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun y => u * y) = G) (h0 : (0 : F) ∉ G) (hne : G.Nonempty)
    {K μ : ℝ} (hμ : (Fintype.card F : ℝ) ≤ (G.card : ℝ) * μ) (hμe : Real.exp 1 ≤ μ)
    (hK : 0 ≤ K)
    (h : DCEnergyBoundWithConstant G ⌈Real.log μ⌉₊ K) :
    WorstCaseIncompleteSumBound ψ G
      (2 * Real.exp 1 * K * (G.card : ℝ) * (Real.log μ + 1)) := by
  intro b hb
  have hlog1 : 1 ≤ Real.log μ := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
    exact Real.log_le_log (Real.exp_pos 1) hμe
  have hr1 : 1 ≤ ⌈Real.log μ⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  have hrμ : Real.log μ ≤ (⌈Real.log μ⌉₊ : ℝ) := Nat.le_ceil _
  have hsq := eta_sq_le_cosetOptimizedWithConstant hψ hbij h0 hne hr1 hμ hrμ hK h hb
  have hrlt : ((⌈Real.log μ⌉₊ : ℕ) : ℝ) < Real.log μ + 1 :=
    Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ Real.log μ)
  have hcoef : (0 : ℝ) ≤ 2 * Real.exp 1 * K * (G.card : ℝ) := by positivity
  calc ‖eta ψ G b‖ ^ 2
      ≤ 2 * Real.exp 1 * K * (G.card : ℝ) * ((⌈Real.log μ⌉₊ : ℕ) : ℝ) := hsq
    _ ≤ 2 * Real.exp 1 * K * (G.card : ℝ) * (Real.log μ + 1) :=
        mul_le_mul_of_nonneg_left hrlt.le hcoef

/-- **The coset-count form** (the headline).  For `G = μ_n` with exactly `m` cosets
(`q = n·m + 1`, `m ≥ 2`), the residual at depth `k₀ = ⌈log(m+1)⌉` gives
`WorstCaseIncompleteSumBound ψ G (2e·K·n·(log(m+1)+1))` — the `√(C·n·log m)` per-frequency
shadow.  New content vs the in-tree `DCEnergyCeilWallWithConstant` consumer: the depth is
`⌈log m⌉`, not `⌈log q⌉` (prize shape: 89 vs 110), with no `√(log q/log m)` loss. -/
theorem worstCase_of_dcEnergyBoundWithConstant_cosetCount
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun y => u * y) = G) (h0 : (0 : F) ∉ G) (hne : G.Nonempty)
    {K : ℝ} {m : ℕ} (hcount : Fintype.card F = G.card * m + 1) (hm : 2 ≤ m) (hK : 0 ≤ K)
    (h : DCEnergyBoundWithConstant G ⌈Real.log ((m : ℝ) + 1)⌉₊ K) :
    WorstCaseIncompleteSumBound ψ G
      (2 * Real.exp 1 * K * (G.card : ℝ) * (Real.log ((m : ℝ) + 1) + 1)) := by
  have hn1 : 1 ≤ G.card := by
    have := Finset.card_pos.mpr hne
    omega
  have hμnat : Fintype.card F ≤ G.card * (m + 1) := by
    calc Fintype.card F = G.card * m + 1 := hcount
      _ ≤ G.card * m + G.card := Nat.add_le_add_left hn1 (G.card * m)
      _ = G.card * (m + 1) := by ring
  have hμ : (Fintype.card F : ℝ) ≤ (G.card : ℝ) * ((m : ℝ) + 1) := by
    calc (Fintype.card F : ℝ) ≤ ((G.card * (m + 1) : ℕ) : ℝ) := by exact_mod_cast hμnat
      _ = (G.card : ℝ) * ((m : ℝ) + 1) := by push_cast; ring
  have hμe : Real.exp 1 ≤ (m : ℝ) + 1 := by
    have h2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith [Real.exp_one_lt_d9]
  exact worstCase_of_dcEnergyBoundWithConstant_logDepth hψ hbij h0 hne hμ hμe hK h

/-- **The unconditional converse floor** (no hypothesis beyond the subgroup structure):
`n·‖η_{b₀}‖^{2r} ≤ q·E_r − n^{2r}` for every `b₀ ≠ 0` and every depth `r`.  The
DC-subtracted energy is bounded BELOW by the sup norm at coset granularity — the moment
hypothesis consumed above can never be strictly weaker than the sup bound it produces. -/
theorem card_mul_eta_pow_le_dcGap
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun y => u * y) = G) (h0 : (0 : F) ∉ G)
    (r : ℕ) {b₀ : F} (hb₀ : b₀ ≠ 0) :
    (G.card : ℝ) * ‖eta ψ G b₀‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) := by
  classical
  have hmoment : ∑ b' : F, ‖eta ψ G b'‖ ^ (2 * r) = (Fintype.card F : ℝ) * rEnergy G r :=
    subgroup_gaussSum_moment hψ G r
  have heta0 : ‖eta ψ G (0 : F)‖ ^ (2 * r) = (G.card : ℝ) ^ (2 * r) := by
    rw [eta_zero, Complex.norm_natCast]
  have hsum_erase : ∑ b' ∈ Finset.univ.erase (0 : F), ‖eta ψ G b'‖ ^ (2 * r)
      = (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0), hmoment, heta0]
  have hcoset := card_mul_eta_pow_le_sum_erase (ψ := ψ) hbij h0 r hb₀
  rwa [hsum_erase] at hcoset

/-- **Converse consumer — the equivalence has no slack.**  A single nonzero frequency above
the matched scale refutes the residual at the same `(r, K)`: the depth-`r` energy
hypothesis is not a weaker surrogate for the sup bound; it is lower-bounded by it. -/
theorem not_dcEnergyBoundWithConstant_of_eta_gt
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun y => u * y) = G) (h0 : (0 : F) ∉ G)
    (r : ℕ) {K : ℝ} {b₀ : F} (hb₀ : b₀ ≠ 0)
    (hgt : (Fintype.card F : ℝ)
        * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))
        < (G.card : ℝ) * ‖eta ψ G b₀‖ ^ (2 * r)) :
    ¬ DCEnergyBoundWithConstant G r K := by
  intro hdc
  unfold DCEnergyBoundWithConstant at hdc
  exact absurd ((card_mul_eta_pow_le_dcGap hψ hbij h0 r hb₀).trans hdc)
    (not_le_of_gt hgt)

end ArkLib.ProximityGap.R376ShadowLogM

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.R376ShadowLogM.coset_eta_pow_le_of_dcEnergyBoundWithConstant
#print axioms ArkLib.ProximityGap.R376ShadowLogM.eta_sq_le_cosetOptimizedWithConstant
#print axioms ArkLib.ProximityGap.R376ShadowLogM.worstCase_of_dcEnergyBoundWithConstant_logDepth
#print axioms ArkLib.ProximityGap.R376ShadowLogM.worstCase_of_dcEnergyBoundWithConstant_cosetCount
#print axioms ArkLib.ProximityGap.R376ShadowLogM.card_mul_eta_pow_le_dcGap
#print axioms ArkLib.ProximityGap.R376ShadowLogM.not_dcEnergyBoundWithConstant_of_eta_gt
