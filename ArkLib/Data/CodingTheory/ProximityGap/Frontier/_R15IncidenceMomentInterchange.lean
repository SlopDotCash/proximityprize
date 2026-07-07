/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# LANE B2 (#466 round 15): the s₀-moment tower for the signed incidence sum — the conditional
  Wick-for-incidence → approximate-Problem-B interchange

Round 13 (`_R13HyperplaneSecondMoment.lean`) proved the exact second moment
`∑_{s₀} ‖I_H(s₀)‖² = q · ∑_{b∈H} ‖η_b‖²` and thereby WORLD II: the sup-norm `M` controls only the
*average* incidence; Problem B (worst-case `‖I_H(s₀)‖ ≤ √|H|·M`, BCHKS Conj 1.12) is a distinct
open input.  This file climbs the whole `s₀`-moment tower

  `S_r := ∑_{s₀ ∈ F} ‖I_H(s₀)‖^{2r}`

and lands the **conditional interchange** (the exact mirror of Problem A's
`_MomentOptimizedSupNorm.lean`, transported from the frequency tower to the offset tower):

> **`incidence_le_of_wickForIncidence`** :  if the Wick-type tower bound
>   `WickForIncidence`: `∀ r, S_r ≤ q · (2r−1)‼ · (∑_{b∈H}‖η_b‖²)^r`
> holds, then for EVERY offset `s₀` (in particular the adversary's worst one)
>   `‖I_H(s₀)‖ ≤ √(2e · (∑_{b∈H}‖η_b‖²) · (ln q + 1)) ≤ √(2e·(ln q+1)) · √|H| · M`,
> i.e. **Problem B up to a `√(2e·ln q)` factor** — the moment method with logarithmic loss.

## The exact combinatorial content of `S_r` (derived, probe-checked, NOT formalized here)

Expanding and using additive-character orthogonality over `s₀`,

  `S_r = q · ∑_{b₁,…,b_r,c₁,…,c_r ∈ H, Σbᵢ ≡ Σcⱼ (mod p)} ∏ conj(η_{bᵢ}) · ∏ η_{cⱼ}`

— the **η-weighted `2r`-th additive energy of the thick hyperplane `H`**.  Moreover, since
`μ_n ⊆ H` (in the prize regime `n | |H|`) and `η_{bu} = η_b` for `u ∈ μ_n`,

  `I_H(s₀) = ∑_{t ∈ H/μ_n} conj(η_t) · η_{t·s₀}`

is a multiplicative autocorrelation of the Gauss-period sequence over the coset group `H/μ_n`: the
tower is a **weighted** energy of thick-`H` (Shkredov territory for the *unweighted* count) with
thin-object `η`-weights carrying the phases.  Probe `probe_r15_b2_incidence_moments.py` measures
where the Wick bound holds/fails at `n = 8/16`, `deg = 2/4`.

## PROBE VERDICT (machine countermodels; `probe_r15_b2_fft.py` / `probe_r15_b2_diagsub.py`)

* **The raw `WickForIncidence` is FALSE** for the true Gauss-period spectrum at every probed scale
  (`n = 8/16/32`, `deg = 2/4`, up to `p = 1048897`): `S_r/Wick` reaches `10^16` by `r = 6`.  The
  failure is a TRIVIAL exact spike, the tower's own "DC term": for `s₀ ∈ μ_n`,
  `I_H(s₀) = Σ/n` EXACTLY (`Σ = ∑_{b∈H}‖η_b‖²`; verified to 1e-11) — the diagonal of the coset
  autocorrelation `I_H(s₀) = ∑_{t∈H/μ_n} conj(η_t) η_{t·s₀}`; and `I_H(0) = ∑_{b∈H} conj(η_b)` is
  a second (smaller) spike.  This is the exact mirror of Problem A's mandatory DC subtraction.
* **The diagonal-subtracted tower obeys Wick everywhere probed**: excluding `D = {0} ∪ μ_n`, all
  ratios `S_r^D/Wick < 1` and decreasing in `r` (`r ≤ 8`), at every probed `(n, deg, p)` including
  `p ≈ n^4`.  The formalized hypothesis to attack is therefore `WickForIncidenceAwayAt` (below).
* Off-diagonal worst-case `‖I_H‖/(√|H|·M)` measured `0.54–1.06` (once `> 1`, at `p = 4129, n = 8,
  deg = 4`): off-diagonal Problem B is essentially TIGHT — constant-1 fails marginally at one
  small scale; any constant `≥ 1.1` holds at all probed scales.

## Honest scope

* `WickForIncidence` (raw) is kept as the base object but is probe-REFUTED for the true spectrum —
  its conditional consumers are empty at the prize.  The meaningful named open hypothesis is the
  **diagonal-subtracted** `WickForIncidenceAwayAt D` with `D = {0} ∪ μ_n`; neither is discharged.
* The conclusion is `√(2e·ln q)`-LOSSY vs Problem B (`√|H|·M` exactly): this route can never give
  the loss-free B, but a proven diagonal-subtracted Wick tower would give the prize-shaped budget
  up to logs for every off-diagonal offset.
* The saddle lemmas (`sq_le_of_pow_ceil`, `doubleFactorial_two_sub_one_le`) are re-proved locally
  (verbatim transport from `_MomentOptimizedSupNorm.lean`) to keep imports minimal.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 15, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### (0) The tower object and the named hypothesis. -/

/-- The signed incidence sum `I_H(s₀) = ∑_{b∈H} conj(η_b)·ψ(b·s₀)`.  This local copy keeps the
round-15 lane independent of scratch-lane oleans. -/
noncomputable def incidenceSum (ψ : AddChar F ℂ) (G H : Finset F) (s₀ : F) : ℂ :=
  ∑ b ∈ H, (starRingEnd ℂ) (eta ψ G b) * ψ (b * s₀)

/-- The second-moment-over-offsets identity:
`∑_{s₀} ‖I_H(s₀)‖² = q · ∑_{b∈H} ‖η_b‖²`.  This is the R13 identity restated locally so this
round-15 lane does not import another frontier scratch file. -/
theorem incidenceSum_sq_sum_offsets {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (H : Finset F) :
    (∑ s₀ : F, ‖incidenceSum ψ G H s₀‖ ^ 2)
      = (Fintype.card F : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 := by
  classical
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a; rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  have hnorm : ∀ s₀ : F,
      incidenceSum ψ G H s₀ * (starRingEnd ℂ) (incidenceSum ψ G H s₀)
        = ((‖incidenceSum ψ G H s₀‖ ^ 2 : ℝ) : ℂ) := by
    intro s₀; rw [RCLike.mul_conj]; norm_cast
  have hconjI : ∀ s₀ : F, (starRingEnd ℂ) (incidenceSum ψ G H s₀)
      = ∑ b' ∈ H, eta ψ G b' * ψ (-(b' * s₀)) := by
    intro s₀
    unfold incidenceSum
    rw [map_sum]
    refine Finset.sum_congr rfl (fun b' _ => ?_)
    rw [map_mul, Complex.conj_conj, hconj (b' * s₀)]
  have hcomplex : (∑ s₀ : F,
      incidenceSum ψ G H s₀ * (starRingEnd ℂ) (incidenceSum ψ G H s₀))
        = (Fintype.card F : ℂ) * ∑ b ∈ H, eta ψ G b * (starRingEnd ℂ) (eta ψ G b) := by
    calc ∑ s₀ : F, incidenceSum ψ G H s₀ * (starRingEnd ℂ) (incidenceSum ψ G H s₀)
        = ∑ s₀ : F, ∑ b ∈ H, ∑ b' ∈ H,
            ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b') * ψ (s₀ * (b - b')) := by
          refine Finset.sum_congr rfl (fun s₀ _ => ?_)
          rw [hconjI s₀]
          unfold incidenceSum
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          refine Finset.sum_congr rfl (fun b' _ => ?_)
          have hpsi : ψ (b * s₀) * ψ (-(b' * s₀)) = ψ (s₀ * (b - b')) := by
            rw [← AddChar.map_add_eq_mul]
            congr 1; ring
          calc (starRingEnd ℂ) (eta ψ G b) * ψ (b * s₀) * (eta ψ G b' * ψ (-(b' * s₀)))
              = ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b') * (ψ (b * s₀) * ψ (-(b' * s₀))) := by
                ring
            _ = ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b') * ψ (s₀ * (b - b')) := by rw [hpsi]
      _ = ∑ b ∈ H, ∑ b' ∈ H,
            ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b') * ∑ s₀ : F, ψ (s₀ * (b - b')) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun b' _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ b ∈ H,
            ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b) * (Fintype.card F : ℂ) := by
          refine Finset.sum_congr rfl (fun b hb => ?_)
          have hb' : ∀ b' ∈ H,
              ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b') * ∑ s₀ : F, ψ (s₀ * (b - b'))
                = (if b' = b then
                    ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b') * (Fintype.card F : ℂ) else 0) := by
            intro b' _
            rw [AddChar.sum_mulShift (b - b') hψ]
            by_cases h : b = b'
            · subst h; simp
            · have hne : b - b' ≠ 0 := sub_ne_zero.mpr h
              rw [if_neg hne, if_neg (fun h' => h h'.symm)]
              simp
          rw [Finset.sum_congr rfl hb',
            Finset.sum_ite_eq' H b
              (fun b' => ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b') * (Fintype.card F : ℂ))]
          rw [if_pos hb]
      _ = (Fintype.card F : ℂ) * ∑ b ∈ H, eta ψ G b * (starRingEnd ℂ) (eta ψ G b) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          ring
  have hcast : ((∑ s₀ : F, ‖incidenceSum ψ G H s₀‖ ^ 2 : ℝ) : ℂ)
      = (Fintype.card F : ℂ) * ∑ b ∈ H, ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    rw [show (∑ s₀ : F, ((‖incidenceSum ψ G H s₀‖ ^ 2 : ℝ) : ℂ))
          = ∑ s₀ : F, incidenceSum ψ G H s₀ * (starRingEnd ℂ) (incidenceSum ψ G H s₀) from
      Finset.sum_congr rfl (fun s₀ _ => (hnorm s₀).symm)]
    rw [hcomplex, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    congr 1
    rw [RCLike.mul_conj]; norm_cast
  have hreal : ((∑ s₀ : F, ‖incidenceSum ψ G H s₀‖ ^ 2 : ℝ) : ℂ)
      = (((Fintype.card F : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
    rw [hcast]; push_cast; ring
  exact_mod_cast hreal

/-- **The `s₀`-moment tower of the signed incidence sum.**
`S_r = ∑_{s₀ ∈ F} ‖I_H(s₀)‖^{2r}`.  `r = 1` is the round-13 exact second moment
(`incidenceSum_sq_sum_offsets`): `S_1 = q·∑_{b∈H}‖η_b‖²`. -/
noncomputable def incidenceMoment (ψ : AddChar F ℂ) (G H : Finset F) (r : ℕ) : ℝ :=
  ∑ s₀ : F, ‖incidenceSum ψ G H s₀‖ ^ (2 * r)

/-- **The named open hypothesis: Wick/Gaussian control of the incidence moment tower.**
`S_r ≤ q · (2r−1)‼ · Σ^r` where `Σ = ∑_{b∈H}‖η_b‖²` (the exact `r = 1` value of `S_r/q`).
This is the offset-side analogue of Problem A's `DCEnergyBound`; it is a `Prop`, consumed as a
hypothesis, NOT discharged.  Probes measure its truth region. -/
def WickForIncidence (ψ : AddChar F ℂ) (G H : Finset F) : Prop :=
  ∀ r : ℕ, incidenceMoment ψ G H r
    ≤ (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
        * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r

/-- Depth-limited single-rung form: only the rung `r` is assumed. -/
def WickForIncidenceAt (ψ : AddChar F ℂ) (G H : Finset F) (r : ℕ) : Prop :=
  incidenceMoment ψ G H r
    ≤ (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
        * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r

/-! ### (1) Trivial but load-bearing: every single offset is dominated by the tower. -/

/-- **Pointwise-to-tower step (the "sup ≤ sum" of the moment method).**
For every offset `s₀` (in particular the adversary's worst), `‖I_H(s₀)‖^{2r} ≤ S_r`, because all
tower terms are nonnegative. -/
theorem pow_le_incidenceMoment (ψ : AddChar F ℂ) (G H : Finset F) (s₀ : F) (r : ℕ) :
    ‖incidenceSum ψ G H s₀‖ ^ (2 * r) ≤ incidenceMoment ψ G H r := by
  classical
  exact Finset.single_le_sum (f := fun s => ‖incidenceSum ψ G H s‖ ^ (2 * r))
    (fun s _ => by positivity) (Finset.mem_univ s₀)

/-! ### (2) The saddle lemmas (verbatim transport from `_MomentOptimizedSupNorm.lean`). -/

/-- `((2r−1)‼ : ℝ) ≤ (2r)ʳ` (Mathlib double factorial). -/
theorem doubleFactorial_two_sub_one_le (r : ℕ) :
    (Nat.doubleFactorial (2 * r - 1) : ℝ) ≤ (2 * r : ℝ) ^ r := by
  have hclosed : Nat.doubleFactorial (2 * r - 1) = ∏ i ∈ Finset.range r, (2 * i + 1) := by
    cases r with
    | zero => simp
    | succ m =>
      have h2 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
      rw [h2, Nat.doubleFactorial_eq_prod_odd m]
      rw [Finset.prod_range_succ']
      simp
  have hcast : (Nat.doubleFactorial (2 * r - 1) : ℝ)
      = ∏ i ∈ Finset.range r, ((2 * i + 1 : ℕ) : ℝ) := by
    rw [hclosed]; push_cast; rfl
  rw [hcast]
  calc ∏ i ∈ Finset.range r, ((2 * i + 1 : ℕ) : ℝ)
      ≤ ∏ _i ∈ Finset.range r, (2 * r : ℝ) := by
        apply Finset.prod_le_prod
        · intro i _; positivity
        · intro i hi
          have hir : i + 1 ≤ r := Finset.mem_range.mp hi
          have : (i : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast hir
          push_cast
          nlinarith [this]
    _ = (2 * r : ℝ) ^ r := by rw [Finset.prod_const, Finset.card_range]

/-- The pure real-analysis optimization core (`q^{1/r} ≤ e` at `r = ⌈ln q⌉`); here `n` plays the
role of the total spectral weight `Σ = ∑_{b∈H}‖η_b‖²`. -/
theorem sq_le_of_pow_ceil {B q n : ℝ} (_hB : 0 ≤ B) (hq : 1 ≤ q) (hn : 0 ≤ n)
    (r : ℕ) (hr : r = ⌈Real.log q⌉₊) (hr1 : 1 ≤ r)
    (hpow : B ^ (2 * r) ≤ q * (2 * r : ℝ) ^ r * n ^ r) :
    B ^ 2 ≤ 2 * Real.exp 1 * n * r := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hrpos
  have hkey : (B ^ 2) ^ r ≤ q * (2 * (n : ℝ) * r) ^ r := by
    rw [← pow_mul]
    calc B ^ (2 * r) ≤ q * (2 * r : ℝ) ^ r * n ^ r := hpow
      _ = q * (2 * n * r) ^ r := by
          rw [mul_pow, mul_pow]; ring
  have hbase_nn : (0 : ℝ) ≤ 2 * (n : ℝ) * r := by positivity
  have hroot : B ^ 2 ≤ (q * (2 * (n : ℝ) * r) ^ r) ^ ((r : ℝ)⁻¹) := by
    calc B ^ 2 = ((B ^ 2) ^ r) ^ ((r : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast (sq_nonneg _) (Nat.one_le_iff_ne_zero.mp hr1)).symm
      _ ≤ (q * (2 * (n : ℝ) * r) ^ r) ^ ((r : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) hkey (by positivity)
  have hsplit : (q * (2 * (n : ℝ) * r) ^ r) ^ ((r : ℝ)⁻¹)
      = q ^ ((r : ℝ)⁻¹) * (2 * (n : ℝ) * r) := by
    rw [Real.mul_rpow (by linarith) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast (2 * (n : ℝ) * r) r, ← Real.rpow_mul hbase_nn]
    rw [mul_inv_cancel₀ hrne, Real.rpow_one]
  have hlogq : Real.log q ≤ r := by
    rw [hr]; exact Nat.le_ceil _
  have hqr_le_e : q ^ ((r : ℝ)⁻¹) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos (by linarith) ((r : ℝ)⁻¹)]
    apply Real.exp_le_exp.mpr
    rw [mul_inv_le_iff₀ hrpos]
    calc Real.log q ≤ r := hlogq
      _ = 1 * r := (one_mul _).symm
  calc B ^ 2 ≤ q ^ ((r : ℝ)⁻¹) * (2 * (n : ℝ) * r) := by rw [← hsplit]; exact hroot
    _ ≤ Real.exp 1 * (2 * (n : ℝ) * r) :=
        mul_le_mul_of_nonneg_right hqr_le_e hbase_nn
    _ = 2 * Real.exp 1 * n * r := by ring

/-! ### (3) The conditional interchange: `WickForIncidence ⟹ approximate Problem B`. -/

/-- **Single-rung interchange.**  From the rung-`r` Wick bound at the moment-optimal depth
`r = ⌈ln q⌉`, EVERY offset obeys `‖I_H(s₀)‖² ≤ 2e·Σ·r` where `Σ = ∑_{b∈H}‖η_b‖²`. -/
theorem incidence_sq_le_of_wickAt {ψ : AddChar F ℂ} (G H : Finset F)
    (r : ℕ) (hr : r = ⌈Real.log (Fintype.card F : ℝ)⌉₊) (hr1 : 1 ≤ r)
    (hq : 1 ≤ (Fintype.card F : ℝ))
    (hwick : WickForIncidenceAt ψ G H r) (s₀ : F) :
    ‖incidenceSum ψ G H s₀‖ ^ 2
      ≤ 2 * Real.exp 1 * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) * r := by
  have hSig : (0 : ℝ) ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 := by positivity
  have hpow : ‖incidenceSum ψ G H s₀‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (2 * r : ℝ) ^ r * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r := by
    calc ‖incidenceSum ψ G H s₀‖ ^ (2 * r)
        ≤ incidenceMoment ψ G H r := pow_le_incidenceMoment ψ G H s₀ r
      _ ≤ (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
            * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r := hwick
      _ ≤ (Fintype.card F : ℝ) * (2 * r : ℝ) ^ r * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r := by
          have h1 := doubleFactorial_two_sub_one_le r
          have h2 : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
          have h3 : (0 : ℝ) ≤ (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r := by positivity
          nlinarith [h1, h2, h3, mul_nonneg h2 h3]
  exact sq_le_of_pow_ceil (norm_nonneg _) hq hSig r hr hr1 hpow

/-- **THE LANE-B2 RESULT (conditional, axiom-clean): `WickForIncidence ⟹ Problem B up to
`√(2e·(ln q + 1))`.**  If the incidence moment tower is Wick-controlled, then for EVERY offset
`s₀` — in particular the far-coset adversary's worst —

  `‖I_H(s₀)‖ ≤ √(2e · (∑_{b∈H}‖η_b‖²) · (ln q + 1))`.

With `∑_{b∈H}‖η_b‖² ≤ |H|·M²` this is `√(2e(ln q+1)) · √|H| · M`: Problem B with a
`√(2e·ln q)`-factor loss.  `WickForIncidence` is the named open input, NOT discharged. -/
theorem incidence_le_of_wickForIncidence {ψ : AddChar F ℂ} (G H : Finset F)
    (hq : Real.exp 1 ≤ (Fintype.card F : ℝ))
    (hwick : WickForIncidence ψ G H) (s₀ : F) :
    ‖incidenceSum ψ G H s₀‖
      ≤ Real.sqrt (2 * Real.exp 1 * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
          * (Real.log (Fintype.card F : ℝ) + 1)) := by
  set r := ⌈Real.log (Fintype.card F : ℝ)⌉₊ with hrdef
  have hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ) := le_trans (Real.one_le_exp (by norm_num)) hq
  have hlog_ge_one : 1 ≤ Real.log (Fintype.card F : ℝ) := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
    exact Real.log_le_log (Real.exp_pos 1) hq
  have hr1 : 1 ≤ r := by
    rw [hrdef]
    exact Nat.one_le_ceil_iff.mpr (by linarith)
  have hsq := incidence_sq_le_of_wickAt G H r hrdef hr1 hq1 (hwick r) s₀
  have hlogq_nn : 0 ≤ Real.log (Fintype.card F : ℝ) := Real.log_nonneg hq1
  have hrlt : (r : ℝ) < Real.log (Fintype.card F : ℝ) + 1 := by
    rw [hrdef]; exact Nat.ceil_lt_add_one hlogq_nn
  have hSig : (0 : ℝ) ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 := by positivity
  have hcoef_nn : (0 : ℝ) ≤ 2 * Real.exp 1 * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) := by positivity
  have hsq2 : ‖incidenceSum ψ G H s₀‖ ^ 2
      ≤ 2 * Real.exp 1 * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
          * (Real.log (Fintype.card F : ℝ) + 1) := by
    calc ‖incidenceSum ψ G H s₀‖ ^ 2
        ≤ 2 * Real.exp 1 * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) * r := hsq
      _ ≤ 2 * Real.exp 1 * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
            * (Real.log (Fintype.card F : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hrlt.le hcoef_nn
  rw [show ‖incidenceSum ψ G H s₀‖ = Real.sqrt (‖incidenceSum ψ G H s₀‖ ^ 2) from
    (Real.sqrt_sq (norm_nonneg _)).symm]
  exact Real.sqrt_le_sqrt hsq2

/-- **The `√|H|·M`-shaped corollary: `WickForIncidence ⟹ ‖I_H(s₀)‖ ≤ √(2e(ln q+1)·|H|)·M` for all
`s₀`** — approximate Problem B, with the sup-norm `M` and the `√(2e ln q)` moment-method loss
explicit.  (`ApproxB` shape; the loss-free Problem B `√|H|·M` is NOT reachable by this route.) -/
theorem approxB_of_wickForIncidence {ψ : AddChar F ℂ} (G H : Finset F)
    (hq : Real.exp 1 ≤ (Fintype.card F : ℝ))
    (hwick : WickForIncidence ψ G H)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ b ∈ H, ‖eta ψ G b‖ ≤ M) (s₀ : F) :
    ‖incidenceSum ψ G H s₀‖
      ≤ Real.sqrt (2 * Real.exp 1 * ((H.card : ℝ) * M ^ 2)
          * (Real.log (Fintype.card F : ℝ) + 1)) := by
  refine le_trans (incidence_le_of_wickForIncidence G H hq hwick s₀) (Real.sqrt_le_sqrt ?_)
  have hsum : (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ≤ (H.card : ℝ) * M ^ 2 := by
    calc (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
        ≤ ∑ _b ∈ H, M ^ 2 := by
          refine Finset.sum_le_sum (fun b hb => ?_)
          have h1 : ‖eta ψ G b‖ ≤ M := hM b hb
          have h0 : 0 ≤ ‖eta ψ G b‖ := norm_nonneg _
          nlinarith [h1, h0]
      _ = (H.card : ℝ) * M ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ) := le_trans (Real.one_le_exp (by norm_num)) hq
  have hlog_nn : 0 ≤ Real.log (Fintype.card F : ℝ) := Real.log_nonneg hq1
  have hcoef : (0 : ℝ) ≤ 2 * Real.exp 1 * (Real.log (Fintype.card F : ℝ) + 1) := by positivity
  nlinarith [hsum, hcoef, Real.exp_pos 1, hlog_nn,
    mul_le_mul_of_nonneg_left hsum (le_of_lt (by positivity :
      (0:ℝ) < 2 * Real.exp 1 * (Real.log (Fintype.card F : ℝ) + 1)))]

/-! ### (4) The diagonal-subtracted tower — the probe-validated object.

The raw tower is probe-REFUTED (docstring above): `s₀ ∈ μ_n` gives the exact spike `I_H(s₀) = Σ/n`,
and `s₀ = 0` a second one.  The honest object excludes a finite diagonal set `D` of offsets
(`D = {0} ∪ μ_n` in the probes) — the tower's own DC subtraction. -/

/-- **The diagonal-subtracted `s₀`-moment tower.**  `S_r^D = ∑_{s₀ ∉ D} ‖I_H(s₀)‖^{2r}`. -/
noncomputable def incidenceMomentAway (ψ : AddChar F ℂ) (G H D : Finset F) (r : ℕ) : ℝ :=
  ∑ s₀ ∈ Finset.univ \ D, ‖incidenceSum ψ G H s₀‖ ^ (2 * r)

/-- **Raw moment = away moment + diagonal mass.**  This is the exact bookkeeping behind the
round-15 correction: the raw tower splits into the diagonal-subtracted tower over
`Finset.univ \ D` plus the excluded offsets in `D`.  Thus any spike on `D` is not mysterious
analytic content; it is the DC/diagonal mass that must be removed before asking for Wick behavior. -/
theorem incidenceMoment_eq_away_add_diag (ψ : AddChar F ℂ) (G H D : Finset F) (r : ℕ) :
    incidenceMoment ψ G H r
      = incidenceMomentAway ψ G H D r
        + ∑ s₀ ∈ D, ‖incidenceSum ψ G H s₀‖ ^ (2 * r) := by
  classical
  unfold incidenceMoment incidenceMomentAway
  let f : F → ℝ := fun s₀ => ‖incidenceSum ψ G H s₀‖ ^ (2 * r)
  have hsplit := Finset.sum_sdiff (s₁ := D) (s₂ := (Finset.univ : Finset F)) (f := f)
    (by intro x _; exact Finset.mem_univ x)
  simpa [f] using hsplit.symm

/-- The diagonal-subtracted moment is bounded by the raw moment.  Formally, the corrected
off-diagonal tower is the raw tower after deleting a nonnegative diagonal contribution. -/
theorem incidenceMomentAway_le_incidenceMoment (ψ : AddChar F ℂ) (G H D : Finset F) (r : ℕ) :
    incidenceMomentAway ψ G H D r ≤ incidenceMoment ψ G H r := by
  classical
  rw [incidenceMoment_eq_away_add_diag ψ G H D r]
  have hdiag_nonneg : 0 ≤ ∑ s₀ ∈ D, ‖incidenceSum ψ G H s₀‖ ^ (2 * r) := by
    positivity
  linarith

/-- **The probe-validated named open hypothesis (rung `r`): diagonal-subtracted Wick.**
`S_r^D ≤ q·(2r−1)‼·Σ^r`.  With `D = {0} ∪ μ_n` this holds at every probed scale with ratio `< 1`
decreasing in `r` — the honest offset-side analogue of Problem A's DC-subtracted `DCEnergyBound`.
Open; NOT discharged. -/
def WickForIncidenceAwayAt (ψ : AddChar F ℂ) (G H D : Finset F) (r : ℕ) : Prop :=
  incidenceMomentAway ψ G H D r
    ≤ (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
        * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r

/-- **Base rung for the corrected tower, proved.**  The diagonal-subtracted Wick hypothesis is
automatic at `r = 1`: the raw second moment is exactly
`q · ∑_{b∈H} ‖η_b‖²`, and deleting the diagonal set `D` can only decrease the nonnegative moment.
Thus the remaining open analytic content of `WickForIncidenceAwayAt` starts at higher moments. -/
theorem wickForIncidenceAwayAt_one {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G H D : Finset F) :
    WickForIncidenceAwayAt ψ G H D 1 := by
  classical
  unfold WickForIncidenceAwayAt
  calc incidenceMomentAway ψ G H D 1
      ≤ incidenceMoment ψ G H 1 := incidenceMomentAway_le_incidenceMoment ψ G H D 1
    _ = (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 1 - 1) : ℝ)
          * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 1 := by
        unfold incidenceMoment
        simpa using incidenceSum_sq_sum_offsets hψ G H

/-- Raw single-rung Wick control implies the diagonal-subtracted single-rung Wick control.  This
fixes the logical hierarchy: away-Wick is the weaker corrected target after deleting the structural
diagonal mass. -/
theorem wickForIncidenceAwayAt_of_wickForIncidenceAt {ψ : AddChar F ℂ} (G H D : Finset F)
    (r : ℕ) (hwick : WickForIncidenceAt ψ G H r) :
    WickForIncidenceAwayAt ψ G H D r :=
  le_trans (incidenceMomentAway_le_incidenceMoment ψ G H D r) hwick

/-- Raw full-tower Wick control implies the corrected diagonal-subtracted rung at every depth. -/
theorem wickForIncidenceAwayAt_of_wickForIncidence {ψ : AddChar F ℂ} (G H D : Finset F)
    (hwick : WickForIncidence ψ G H) (r : ℕ) :
    WickForIncidenceAwayAt ψ G H D r :=
  wickForIncidenceAwayAt_of_wickForIncidenceAt G H D r (hwick r)

/-- Pointwise-to-tower step, diagonal-subtracted: for `s₀ ∉ D`,
`‖I_H(s₀)‖^{2r} ≤ S_r^D`. -/
theorem pow_le_incidenceMomentAway (ψ : AddChar F ℂ) (G H D : Finset F) {s₀ : F}
    (hs : s₀ ∉ D) (r : ℕ) :
    ‖incidenceSum ψ G H s₀‖ ^ (2 * r) ≤ incidenceMomentAway ψ G H D r := by
  classical
  exact Finset.single_le_sum (f := fun s => ‖incidenceSum ψ G H s‖ ^ (2 * r))
    (fun s _ => by positivity)
    (Finset.mem_sdiff.mpr ⟨Finset.mem_univ s₀, hs⟩)

/-- **The diagonal-subtracted interchange (THE probe-consistent conditional).**  From the
diagonal-subtracted Wick rung at the optimal depth `r = ⌈ln q⌉`, every OFF-diagonal offset
`s₀ ∉ D` obeys `‖I_H(s₀)‖² ≤ 2e·Σ·r` — approximate Problem B away from the diagonal, the only
regime where it can hold at all (`s₀ ∈ μ_n` provably reaches `Σ/n ≈ |H|`-scale). -/
theorem incidence_sq_le_of_wickAwayAt {ψ : AddChar F ℂ} (G H D : Finset F)
    (r : ℕ) (hr : r = ⌈Real.log (Fintype.card F : ℝ)⌉₊) (hr1 : 1 ≤ r)
    (hq : 1 ≤ (Fintype.card F : ℝ))
    (hwick : WickForIncidenceAwayAt ψ G H D r) {s₀ : F} (hs : s₀ ∉ D) :
    ‖incidenceSum ψ G H s₀‖ ^ 2
      ≤ 2 * Real.exp 1 * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) * r := by
  have hSig : (0 : ℝ) ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 := by positivity
  have hpow : ‖incidenceSum ψ G H s₀‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (2 * r : ℝ) ^ r * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r := by
    calc ‖incidenceSum ψ G H s₀‖ ^ (2 * r)
        ≤ incidenceMomentAway ψ G H D r := pow_le_incidenceMomentAway ψ G H D hs r
      _ ≤ (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
            * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r := hwick
      _ ≤ (Fintype.card F : ℝ) * (2 * r : ℝ) ^ r * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r := by
          have h1 := doubleFactorial_two_sub_one_le r
          have h2 : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
          have h3 : (0 : ℝ) ≤ (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r := by positivity
          nlinarith [h1, h2, h3, mul_nonneg h2 h3]
  exact sq_le_of_pow_ceil (norm_nonneg _) hq hSig r hr hr1 hpow

/-- **Square-rooted diagonal-subtracted interchange.**  This is the corrected analogue of
`incidence_le_of_wickForIncidence`: assuming the diagonal-subtracted Wick rung at the
moment-optimal depth, every offset away from the diagonal set `D` satisfies the approximate
Problem-B bound

`‖I_H(s₀)‖ ≤ √(2e · Σ · (⌈log q⌉))`,

where `Σ = ∑_{b∈H} ‖η_b‖²`.  The raw all-offset statement is false by the B1 diagonal spike; this
is the probe-consistent off-diagonal target. -/
theorem incidence_le_of_wickAwayAt {ψ : AddChar F ℂ} (G H D : Finset F)
    (r : ℕ) (hr : r = ⌈Real.log (Fintype.card F : ℝ)⌉₊) (hr1 : 1 ≤ r)
    (hq : 1 ≤ (Fintype.card F : ℝ))
    (hwick : WickForIncidenceAwayAt ψ G H D r) {s₀ : F} (hs : s₀ ∉ D) :
    ‖incidenceSum ψ G H s₀‖
      ≤ Real.sqrt (2 * Real.exp 1 * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) * r) := by
  have hsq := incidence_sq_le_of_wickAwayAt G H D r hr hr1 hq hwick hs
  rw [show ‖incidenceSum ψ G H s₀‖ = Real.sqrt (‖incidenceSum ψ G H s₀‖ ^ 2) from
    (Real.sqrt_sq (norm_nonneg _)).symm]
  exact Real.sqrt_le_sqrt hsq

/-- **The corrected approximate Problem-B corollary away from the diagonal.**  If the
diagonal-subtracted Wick rung holds at the moment-optimal depth and the Fourier coefficients on
`H` obey the sup bound `‖η_b‖ ≤ M`, then every off-diagonal offset `s₀ ∉ D` satisfies

`‖I_H(s₀)‖ ≤ √(2e · |H| · M² · ⌈log q⌉)`.

This is the usable probe-consistent replacement for the refuted all-offset `ApproxB` interface. -/
theorem approxB_away_of_wickAwayAt {ψ : AddChar F ℂ} (G H D : Finset F)
    (r : ℕ) (hr : r = ⌈Real.log (Fintype.card F : ℝ)⌉₊) (hr1 : 1 ≤ r)
    (hq : 1 ≤ (Fintype.card F : ℝ))
    (hwick : WickForIncidenceAwayAt ψ G H D r)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ b ∈ H, ‖eta ψ G b‖ ≤ M)
    {s₀ : F} (hs : s₀ ∉ D) :
    ‖incidenceSum ψ G H s₀‖
      ≤ Real.sqrt (2 * Real.exp 1 * ((H.card : ℝ) * M ^ 2) * r) := by
  refine le_trans (incidence_le_of_wickAwayAt G H D r hr hr1 hq hwick hs)
    (Real.sqrt_le_sqrt ?_)
  have hsum : (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ≤ (H.card : ℝ) * M ^ 2 := by
    calc (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
        ≤ ∑ _b ∈ H, M ^ 2 := by
          refine Finset.sum_le_sum (fun b hb => ?_)
          have h1 : ‖eta ψ G b‖ ≤ M := hM b hb
          have h0 : 0 ≤ ‖eta ψ G b‖ := norm_nonneg _
          nlinarith [h1, h0]
      _ = (H.card : ℝ) * M ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcoef : (0 : ℝ) ≤ 2 * Real.exp 1 * r := by positivity
  nlinarith [hsum, hcoef,
    mul_le_mul_of_nonneg_left hsum (le_of_lt (by positivity :
      (0 : ℝ) < 2 * Real.exp 1 * r))]

/-- **Optimized-depth off-diagonal interchange.**  This is the diagonal-subtracted analogue of
`incidence_le_of_wickForIncidence`, but it needs only the single Wick rung at
`r = ⌈log q⌉₊`.  The conclusion replaces the explicit ceiling by the smoother
`log q + 1`, using `⌈log q⌉ < log q + 1`. -/
theorem incidence_le_of_wickAwayAt_optimal {ψ : AddChar F ℂ} (G H D : Finset F)
    (hq : Real.exp 1 ≤ (Fintype.card F : ℝ))
    (hwick : WickForIncidenceAwayAt ψ G H D ⌈Real.log (Fintype.card F : ℝ)⌉₊)
    {s₀ : F} (hs : s₀ ∉ D) :
    ‖incidenceSum ψ G H s₀‖
      ≤ Real.sqrt (2 * Real.exp 1 * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
          * (Real.log (Fintype.card F : ℝ) + 1)) := by
  set r := ⌈Real.log (Fintype.card F : ℝ)⌉₊ with hrdef
  have hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ) := le_trans (Real.one_le_exp (by norm_num)) hq
  have hlog_ge_one : 1 ≤ Real.log (Fintype.card F : ℝ) := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
    exact Real.log_le_log (Real.exp_pos 1) hq
  have hr1 : 1 ≤ r := by
    rw [hrdef]
    exact Nat.one_le_ceil_iff.mpr (by linarith)
  have hwickr : WickForIncidenceAwayAt ψ G H D r := by
    simpa [hrdef] using hwick
  have hsq := incidence_sq_le_of_wickAwayAt G H D r hrdef hr1 hq1 hwickr hs
  have hlogq_nn : 0 ≤ Real.log (Fintype.card F : ℝ) := Real.log_nonneg hq1
  have hrlt : (r : ℝ) < Real.log (Fintype.card F : ℝ) + 1 := by
    rw [hrdef]; exact Nat.ceil_lt_add_one hlogq_nn
  have hcoef_nn : (0 : ℝ) ≤ 2 * Real.exp 1 * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) := by
    positivity
  have hsq2 : ‖incidenceSum ψ G H s₀‖ ^ 2
      ≤ 2 * Real.exp 1 * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
          * (Real.log (Fintype.card F : ℝ) + 1) := by
    calc ‖incidenceSum ψ G H s₀‖ ^ 2
        ≤ 2 * Real.exp 1 * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) * r := hsq
      _ ≤ 2 * Real.exp 1 * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
            * (Real.log (Fintype.card F : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hrlt.le hcoef_nn
  rw [show ‖incidenceSum ψ G H s₀‖ = Real.sqrt (‖incidenceSum ψ G H s₀‖ ^ 2) from
    (Real.sqrt_sq (norm_nonneg _)).symm]
  exact Real.sqrt_le_sqrt hsq2

/-- **Optimized-depth corrected `ApproxB` interface.**  A single diagonal-subtracted Wick rung at
`⌈log q⌉₊`, plus the coefficient sup bound `‖η_b‖ ≤ M` on `H`, gives the log-loss
off-diagonal Problem-B estimate with no caller-side ceiling bookkeeping. -/
theorem approxB_away_of_wickAwayAt_optimal {ψ : AddChar F ℂ} (G H D : Finset F)
    (hq : Real.exp 1 ≤ (Fintype.card F : ℝ))
    (hwick : WickForIncidenceAwayAt ψ G H D ⌈Real.log (Fintype.card F : ℝ)⌉₊)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ b ∈ H, ‖eta ψ G b‖ ≤ M)
    {s₀ : F} (hs : s₀ ∉ D) :
    ‖incidenceSum ψ G H s₀‖
      ≤ Real.sqrt (2 * Real.exp 1 * ((H.card : ℝ) * M ^ 2)
          * (Real.log (Fintype.card F : ℝ) + 1)) := by
  refine le_trans (incidence_le_of_wickAwayAt_optimal G H D hq hwick hs)
    (Real.sqrt_le_sqrt ?_)
  have hsum : (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ≤ (H.card : ℝ) * M ^ 2 := by
    calc (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
        ≤ ∑ _b ∈ H, M ^ 2 := by
          refine Finset.sum_le_sum (fun b hb => ?_)
          have h1 : ‖eta ψ G b‖ ≤ M := hM b hb
          have h0 : 0 ≤ ‖eta ψ G b‖ := norm_nonneg _
          nlinarith [h1, h0]
      _ = (H.card : ℝ) * M ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ) := le_trans (Real.one_le_exp (by norm_num)) hq
  have hlog_nn : 0 ≤ Real.log (Fintype.card F : ℝ) := Real.log_nonneg hq1
  have hcoef : (0 : ℝ) ≤ 2 * Real.exp 1 * (Real.log (Fintype.card F : ℝ) + 1) := by
    positivity
  nlinarith [hsum, hcoef, Real.exp_pos 1, hlog_nn,
    mul_le_mul_of_nonneg_left hsum (le_of_lt (by positivity :
      (0 : ℝ) < 2 * Real.exp 1 * (Real.log (Fintype.card F : ℝ) + 1)))]

/-- **Raw full-tower Wick gives the corrected optimized off-diagonal incidence bound.**  This
packages the logical chain

`WickForIncidence → WickForIncidenceAwayAt(⌈log q⌉₊) → off-diagonal incidence`.

It is intentionally recorded even though raw Wick is probe-refuted for the true spectrum: the lemma
shows exactly that the corrected theorem is a weakening of the older raw tower route, with the only
new content being removal of the diagonal mass. -/
theorem incidence_le_away_optimal_of_wickForIncidence {ψ : AddChar F ℂ} (G H D : Finset F)
    (hq : Real.exp 1 ≤ (Fintype.card F : ℝ))
    (hwick : WickForIncidence ψ G H) {s₀ : F} (hs : s₀ ∉ D) :
    ‖incidenceSum ψ G H s₀‖
      ≤ Real.sqrt (2 * Real.exp 1 * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
          * (Real.log (Fintype.card F : ℝ) + 1)) := by
  exact incidence_le_of_wickAwayAt_optimal G H D hq
    (wickForIncidenceAwayAt_of_wickForIncidence G H D hwick
      ⌈Real.log (Fintype.card F : ℝ)⌉₊) hs

/-- **Raw full-tower Wick gives corrected optimized `ApproxB` away from the diagonal.**  This is
the composed consumer-facing statement: raw Wick plus the coefficient sup bound implies the
log-loss Problem-B estimate for every `s₀ ∉ D`. -/
theorem approxB_away_optimal_of_wickForIncidence {ψ : AddChar F ℂ} (G H D : Finset F)
    (hq : Real.exp 1 ≤ (Fintype.card F : ℝ))
    (hwick : WickForIncidence ψ G H)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ b ∈ H, ‖eta ψ G b‖ ≤ M)
    {s₀ : F} (hs : s₀ ∉ D) :
    ‖incidenceSum ψ G H s₀‖
      ≤ Real.sqrt (2 * Real.exp 1 * ((H.card : ℝ) * M ^ 2)
          * (Real.log (Fintype.card F : ℝ) + 1)) := by
  exact approxB_away_of_wickAwayAt_optimal G H D hq
    (wickForIncidenceAwayAt_of_wickForIncidence G H D hwick
      ⌈Real.log (Fintype.card F : ℝ)⌉₊) hM0 hM hs

/-- **Raw optimal single-rung Wick gives corrected optimized `ApproxB` away from the diagonal.**
This variant is the tightest bridge for future attempts: it consumes only
`WickForIncidenceAt` at `⌈log q⌉₊`, then deletes the diagonal mass and applies the optimized
off-diagonal endpoint. -/
theorem approxB_away_optimal_of_wickForIncidenceAt {ψ : AddChar F ℂ} (G H D : Finset F)
    (hq : Real.exp 1 ≤ (Fintype.card F : ℝ))
    (hwick : WickForIncidenceAt ψ G H ⌈Real.log (Fintype.card F : ℝ)⌉₊)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ b ∈ H, ‖eta ψ G b‖ ≤ M)
    {s₀ : F} (hs : s₀ ∉ D) :
    ‖incidenceSum ψ G H s₀‖
      ≤ Real.sqrt (2 * Real.exp 1 * ((H.card : ℝ) * M ^ 2)
          * (Real.log (Fintype.card F : ℝ) + 1)) := by
  exact approxB_away_of_wickAwayAt_optimal G H D hq
    (wickForIncidenceAwayAt_of_wickForIncidenceAt G H D
      ⌈Real.log (Fintype.card F : ℝ)⌉₊ hwick) hM0 hM hs

end ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.pow_le_incidenceMoment
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.incidence_sq_le_of_wickAt
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.incidence_le_of_wickForIncidence
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.approxB_of_wickForIncidence
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.incidenceMoment_eq_away_add_diag
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.incidenceMomentAway_le_incidenceMoment
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_one
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_of_wickForIncidenceAt
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_of_wickForIncidence
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.pow_le_incidenceMomentAway
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.incidence_sq_le_of_wickAwayAt
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.incidence_le_of_wickAwayAt
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.approxB_away_of_wickAwayAt
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.incidence_le_of_wickAwayAt_optimal
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.approxB_away_of_wickAwayAt_optimal
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.incidence_le_away_optimal_of_wickForIncidence
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.approxB_away_optimal_of_wickForIncidence
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.approxB_away_optimal_of_wickForIncidenceAt
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.incidenceSum_sq_sum_offsets
