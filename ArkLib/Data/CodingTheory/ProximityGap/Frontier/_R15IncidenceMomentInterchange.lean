/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
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
* **The first diagonal-subtracted probes looked Wick-controlled**, but the wider round-16
  stress sweep found a valid secondary-spike counterexample for the naive deletion set
  `D = {0} ∪ μ_n`: `p = 7681, n = 64, deg = 8` has
  `S₂^D/(3qΣ²) = 1.00481`.  Thus `WickForIncidenceAwayAt` remains a useful formal
  interface, but not a universal conjecture for this smallest deletion set without an
  additional range hypothesis or enlarged diagonal/secondary-spike deletion.
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

/-- **Away moments are monotone in the deleted diagonal set.**  Enlarging `D` only removes
nonnegative terms from the diagonal-subtracted tower.  This lets future analytic proofs target the
minimal structural diagonal while downstream consumers use any safer superset. -/
theorem incidenceMomentAway_antitone_deleted (ψ : AddChar F ℂ) (G H : Finset F)
    {D D' : Finset F} (hDD' : D ⊆ D') (r : ℕ) :
    incidenceMomentAway ψ G H D' r ≤ incidenceMomentAway ψ G H D r := by
  classical
  unfold incidenceMomentAway
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro s hs
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ s, fun hsD => (Finset.mem_sdiff.mp hs).2 (hDD' hsD)⟩
  · intro s _ _
    positivity

/-- **The probe-validated named open hypothesis (rung `r`): diagonal-subtracted Wick.**
`S_r^D ≤ q·(2r−1)‼·Σ^r`.  With `D = {0} ∪ μ_n` this holds at every probed scale with ratio `< 1`
decreasing in `r` — the honest offset-side analogue of Problem A's DC-subtracted `DCEnergyBound`.
Open; NOT discharged. -/
def WickForIncidenceAwayAt (ψ : AddChar F ℂ) (G H D : Finset F) (r : ℕ) : Prop :=
  incidenceMomentAway ψ G H D r
    ≤ (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
        * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r

/-- **Full corrected incidence Wick tower.**  This is the honest replacement for the refuted raw
`WickForIncidence`: all moment rungs after deleting the structural diagonal set `D`. -/
def WickForIncidenceAway (ψ : AddChar F ℂ) (G H D : Finset F) : Prop :=
  ∀ r : ℕ, WickForIncidenceAwayAt ψ G H D r

/-- **Raw moment with exact diagonal mass allowed.**  This is the expansion-friendly form of the
corrected rung: the raw incidence moment may exceed Wick by exactly the deleted diagonal block. -/
def RawIncidenceMomentWithDiagonalAt (ψ : AddChar F ℂ) (G H D : Finset F) (r : ℕ) : Prop :=
  incidenceMoment ψ G H r
    ≤ (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
        * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r
      + ∑ s₀ ∈ D, ‖incidenceSum ψ G H s₀‖ ^ (2 * r)

/-- Full raw-with-diagonal tower, equivalent rungwise to the corrected away tower. -/
def RawIncidenceMomentWithDiagonal (ψ : AddChar F ℂ) (G H D : Finset F) : Prop :=
  ∀ r : ℕ, RawIncidenceMomentWithDiagonalAt ψ G H D r

/-- **Named first open fourth-moment target.**  This is the `r = 2` raw-with-diagonal estimate:
`S₂ ≤ 3 q Σ² + diagonalMass₂(D)`. -/
def RawFourthMomentWithDiagonal (ψ : AddChar F ℂ) (G H D : Finset F) : Prop :=
  incidenceMoment ψ G H 2
    ≤ (Fintype.card F : ℝ) * 3 * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2
      + ∑ s₀ ∈ D, ‖incidenceSum ψ G H s₀‖ ^ 4

/-- **Named pointwise route to the first hard rung.**  Away from `D`, every incidence value is
variance-scale: `‖I_H(s₀)‖² ≤ 3Σ`, where `Σ = ∑_{b∈H} ‖η_b‖²`. -/
def OffdiagSquareLeThreeSigma (ψ : AddChar F ℂ) (G H D : Finset F) : Prop :=
  ∀ s₀ : F, s₀ ∉ D →
    ‖incidenceSum ψ G H s₀‖ ^ 2 ≤ 3 * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2

/-- **Norm-scale off-diagonal target.**  This is the more analytic-looking version of
`OffdiagSquareLeThreeSigma`: away from `D`, the incidence norm is bounded by
`C · sqrt(Σ)`.  The square target follows whenever `0 ≤ C` and `C² ≤ 3`. -/
def OffdiagNormLeSqrtSigma (ψ : AddChar F ℂ) (G H D : Finset F) (C : ℝ) : Prop :=
  ∀ s₀ : F, s₀ ∉ D →
    ‖incidenceSum ψ G H s₀‖
      ≤ C * Real.sqrt (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)

/-- **Exact-constant norm-scale first-rung target.**  Away from `D`,
`‖I_H(s₀)‖ ≤ sqrt(3) * sqrt(Σ)`, the constant needed to imply
`OffdiagSquareLeThreeSigma`. -/
def OffdiagNormLeSqrtThreeSigma (ψ : AddChar F ℂ) (G H D : Finset F) : Prop :=
  OffdiagNormLeSqrtSigma ψ G H D (Real.sqrt 3)

/-- **Problem-B-shaped off-diagonal norm target.**  Away from `D`,
`‖I_H(s₀)‖ ≤ sqrt(Σ)`.  This is stronger than the `sqrt(3)` first-rung target. -/
def OffdiagNormLeSqrtSigmaOne (ψ : AddChar F ℂ) (G H D : Finset F) : Prop :=
  OffdiagNormLeSqrtSigma ψ G H D 1

/-- **Problem-B-shaped off-diagonal target with an explicit coefficient sup bound.**  If
`M` bounds `‖η_b‖` on `H`, this is the familiar square-root-cancellation scale
`sqrt(|H| · M²)`. -/
def OffdiagNormLeSqrtCardMulSup (ψ : AddChar F ℂ) (G H D : Finset F) (M : ℝ) : Prop :=
  ∀ s₀ : F, s₀ ∉ D →
    ‖incidenceSum ψ G H s₀‖ ≤ Real.sqrt ((H.card : ℝ) * M ^ 2)

/-- **Familiar Problem-B product form.**  Away from `D`,
`‖I_H(s₀)‖ ≤ sqrt(|H|) · M`.  This is equivalent to
`OffdiagNormLeSqrtCardMulSup` when `M ≥ 0`, but is often the most readable statement. -/
def OffdiagNormLeSqrtCardMulSupProduct (ψ : AddChar F ℂ) (G H D : Finset F) (M : ℝ) :
    Prop :=
  ∀ s₀ : F, s₀ ∉ D →
    ‖incidenceSum ψ G H s₀‖ ≤ Real.sqrt (H.card : ℝ) * M

/-- **Constant-`C` familiar Problem-B product form.**  Away from `D`,
`‖I_H(s₀)‖ ≤ C · sqrt(|H|) · M`. -/
def OffdiagNormLeConstSqrtCardMulSupProduct
    (ψ : AddChar F ℂ) (G H D : Finset F) (C M : ℝ) : Prop :=
  ∀ s₀ : F, s₀ ∉ D →
    ‖incidenceSum ψ G H s₀‖ ≤ C * (Real.sqrt (H.card : ℝ) * M)

/-- **`sqrt(3)` product-form first-rung target.**  Away from `D`,
`‖I_H(s₀)‖ ≤ sqrt(3) · sqrt(|H|) · M`. -/
def OffdiagNormLeSqrtThreeCardMulSupProduct
    (ψ : AddChar F ℂ) (G H D : Finset F) (M : ℝ) : Prop :=
  OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D (Real.sqrt 3) M

/-- Monotonicity of the norm-scale target in the constant. -/
theorem offdiagNormLeSqrtSigma_mono_const {ψ : AddChar F ℂ} (G H D : Finset F)
    {C C' : ℝ} (hCC' : C ≤ C')
    (hpt : OffdiagNormLeSqrtSigma ψ G H D C) :
    OffdiagNormLeSqrtSigma ψ G H D C' := by
  intro s₀ hs₀
  refine le_trans (hpt s₀ hs₀) ?_
  exact mul_le_mul_of_nonneg_right hCC'
    (Real.sqrt_nonneg (∑ b ∈ H, ‖eta ψ G b‖ ^ 2))

/-- Any norm-scale bound with constant `C ≤ sqrt(3)` implies the exact-constant target. -/
theorem offdiagNormLeSqrtThreeSigma_of_offdiagNormLeSqrtSigma_le {ψ : AddChar F ℂ}
    (G H D : Finset F) {C : ℝ} (hC : C ≤ Real.sqrt 3)
    (hpt : OffdiagNormLeSqrtSigma ψ G H D C) :
    OffdiagNormLeSqrtThreeSigma ψ G H D :=
  offdiagNormLeSqrtSigma_mono_const G H D hC hpt

/-- Constant-1 off-diagonal norm control implies the exact `sqrt(3)` target. -/
theorem offdiagNormLeSqrtThreeSigma_of_offdiagNormLeSqrtSigmaOne
    {ψ : AddChar F ℂ} (G H D : Finset F)
    (hpt : OffdiagNormLeSqrtSigmaOne ψ G H D) :
    OffdiagNormLeSqrtThreeSigma ψ G H D := by
  refine offdiagNormLeSqrtThreeSigma_of_offdiagNormLeSqrtSigma_le G H D ?_ hpt
  rw [← Real.sqrt_one]
  exact Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ 3)

/-- Monotonicity of the squared off-diagonal target in the deleted set. -/
theorem offdiagSquareLeThreeSigma_mono_deleted {ψ : AddChar F ℂ} (G H : Finset F)
    {D D' : Finset F} (hDD' : D ⊆ D')
    (hpt : OffdiagSquareLeThreeSigma ψ G H D) :
    OffdiagSquareLeThreeSigma ψ G H D' := by
  intro s₀ hs₀
  exact hpt s₀ (fun hsD => hs₀ (hDD' hsD))

/-- Monotonicity of the norm-scale off-diagonal target in the deleted set. -/
theorem offdiagNormLeSqrtSigma_mono_deleted {ψ : AddChar F ℂ} (G H : Finset F)
    {D D' : Finset F} (hDD' : D ⊆ D') (C : ℝ)
    (hpt : OffdiagNormLeSqrtSigma ψ G H D C) :
    OffdiagNormLeSqrtSigma ψ G H D' C := by
  intro s₀ hs₀
  exact hpt s₀ (fun hsD => hs₀ (hDD' hsD))

/-- Monotonicity of the exact `sqrt(3)` norm-scale target in the deleted set. -/
theorem offdiagNormLeSqrtThreeSigma_mono_deleted {ψ : AddChar F ℂ} (G H : Finset F)
    {D D' : Finset F} (hDD' : D ⊆ D')
    (hpt : OffdiagNormLeSqrtThreeSigma ψ G H D) :
    OffdiagNormLeSqrtThreeSigma ψ G H D' :=
  offdiagNormLeSqrtSigma_mono_deleted G H hDD' (Real.sqrt 3) hpt

/-- Monotonicity of the constant-1 norm-scale target in the deleted set. -/
theorem offdiagNormLeSqrtSigmaOne_mono_deleted {ψ : AddChar F ℂ} (G H : Finset F)
    {D D' : Finset F} (hDD' : D ⊆ D')
    (hpt : OffdiagNormLeSqrtSigmaOne ψ G H D) :
    OffdiagNormLeSqrtSigmaOne ψ G H D' :=
  offdiagNormLeSqrtSigma_mono_deleted G H hDD' 1 hpt

/-- Monotonicity of the square-root-card target in the deleted set. -/
theorem offdiagNormLeSqrtCardMulSup_mono_deleted {ψ : AddChar F ℂ} (G H : Finset F)
    {D D' : Finset F} (hDD' : D ⊆ D') (M : ℝ)
    (hpt : OffdiagNormLeSqrtCardMulSup ψ G H D M) :
    OffdiagNormLeSqrtCardMulSup ψ G H D' M := by
  intro s₀ hs₀
  exact hpt s₀ (fun hsD => hs₀ (hDD' hsD))

/-- Monotonicity of the familiar product-form target in the deleted set. -/
theorem offdiagNormLeSqrtCardMulSupProduct_mono_deleted {ψ : AddChar F ℂ} (G H : Finset F)
    {D D' : Finset F} (hDD' : D ⊆ D') (M : ℝ)
    (hpt : OffdiagNormLeSqrtCardMulSupProduct ψ G H D M) :
    OffdiagNormLeSqrtCardMulSupProduct ψ G H D' M := by
  intro s₀ hs₀
  exact hpt s₀ (fun hsD => hs₀ (hDD' hsD))

/-- Monotonicity of the constant product-form target in the deleted set. -/
theorem offdiagNormLeConstSqrtCardMulSupProduct_mono_deleted {ψ : AddChar F ℂ}
    (G H : Finset F) {D D' : Finset F} (hDD' : D ⊆ D') (C M : ℝ)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D' C M := by
  intro s₀ hs₀
  exact hpt s₀ (fun hsD => hs₀ (hDD' hsD))

/-- Monotonicity of the `sqrt(3)` product-form target in the deleted set. -/
theorem offdiagNormLeSqrtThreeCardMulSupProduct_mono_deleted {ψ : AddChar F ℂ}
    (G H : Finset F) {D D' : Finset F} (hDD' : D ⊆ D') (M : ℝ)
    (hpt : OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M) :
    OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D' M :=
  offdiagNormLeConstSqrtCardMulSupProduct_mono_deleted G H hDD' (Real.sqrt 3) M hpt

/-- Enlarge the squared off-diagonal target by deleting an additional spike set `E`. -/
theorem offdiagSquareLeThreeSigma_union_deleted {ψ : AddChar F ℂ} (G H D E : Finset F)
    (hpt : OffdiagSquareLeThreeSigma ψ G H D) :
    OffdiagSquareLeThreeSigma ψ G H (D ∪ E) :=
  offdiagSquareLeThreeSigma_mono_deleted G H (by intro s hs; exact Finset.mem_union_left E hs)
    hpt

/-- Enlarge the norm-scale off-diagonal target by deleting an additional spike set `E`. -/
theorem offdiagNormLeSqrtSigma_union_deleted {ψ : AddChar F ℂ} (G H D E : Finset F)
    (C : ℝ) (hpt : OffdiagNormLeSqrtSigma ψ G H D C) :
    OffdiagNormLeSqrtSigma ψ G H (D ∪ E) C :=
  offdiagNormLeSqrtSigma_mono_deleted G H
    (by intro s hs; exact Finset.mem_union_left E hs) C hpt

/-- Enlarge the exact `sqrt(3)` norm-scale target by deleting an additional spike set `E`. -/
theorem offdiagNormLeSqrtThreeSigma_union_deleted {ψ : AddChar F ℂ} (G H D E : Finset F)
    (hpt : OffdiagNormLeSqrtThreeSigma ψ G H D) :
    OffdiagNormLeSqrtThreeSigma ψ G H (D ∪ E) :=
  offdiagNormLeSqrtThreeSigma_mono_deleted G H
    (by intro s hs; exact Finset.mem_union_left E hs) hpt

/-- Enlarge the constant-1 norm-scale target by deleting an additional spike set `E`. -/
theorem offdiagNormLeSqrtSigmaOne_union_deleted {ψ : AddChar F ℂ} (G H D E : Finset F)
    (hpt : OffdiagNormLeSqrtSigmaOne ψ G H D) :
    OffdiagNormLeSqrtSigmaOne ψ G H (D ∪ E) :=
  offdiagNormLeSqrtSigmaOne_mono_deleted G H
    (by intro s hs; exact Finset.mem_union_left E hs) hpt

/-- Enlarge the square-root-card target by deleting an additional spike set `E`. -/
theorem offdiagNormLeSqrtCardMulSup_union_deleted {ψ : AddChar F ℂ}
    (G H D E : Finset F) (M : ℝ)
    (hpt : OffdiagNormLeSqrtCardMulSup ψ G H D M) :
    OffdiagNormLeSqrtCardMulSup ψ G H (D ∪ E) M :=
  offdiagNormLeSqrtCardMulSup_mono_deleted G H
    (by intro s hs; exact Finset.mem_union_left E hs) M hpt

/-- Enlarge the familiar product-form target by deleting an additional spike set `E`. -/
theorem offdiagNormLeSqrtCardMulSupProduct_union_deleted {ψ : AddChar F ℂ}
    (G H D E : Finset F) (M : ℝ)
    (hpt : OffdiagNormLeSqrtCardMulSupProduct ψ G H D M) :
    OffdiagNormLeSqrtCardMulSupProduct ψ G H (D ∪ E) M :=
  offdiagNormLeSqrtCardMulSupProduct_mono_deleted G H
    (by intro s hs; exact Finset.mem_union_left E hs) M hpt

/-- Enlarge the constant product-form target by deleting an additional spike set `E`. -/
theorem offdiagNormLeConstSqrtCardMulSupProduct_union_deleted {ψ : AddChar F ℂ}
    (G H D E : Finset F) (C M : ℝ)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    OffdiagNormLeConstSqrtCardMulSupProduct ψ G H (D ∪ E) C M :=
  offdiagNormLeConstSqrtCardMulSupProduct_mono_deleted G H
    (by intro s hs; exact Finset.mem_union_left E hs) C M hpt

/-- Enlarge the `sqrt(3)` product-form target by deleting an additional spike set `E`. -/
theorem offdiagNormLeSqrtThreeCardMulSupProduct_union_deleted {ψ : AddChar F ℂ}
    (G H D E : Finset F) (M : ℝ)
    (hpt : OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M) :
    OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H (D ∪ E) M :=
  offdiagNormLeSqrtThreeCardMulSupProduct_mono_deleted G H
    (by intro s hs; exact Finset.mem_union_left E hs) M hpt

/-- Enlarge the squared off-diagonal target by deleting an additional left-hand spike set `E`. -/
theorem offdiagSquareLeThreeSigma_leftUnion_deleted {ψ : AddChar F ℂ} (G H D E : Finset F)
    (hpt : OffdiagSquareLeThreeSigma ψ G H D) :
    OffdiagSquareLeThreeSigma ψ G H (E ∪ D) :=
  offdiagSquareLeThreeSigma_mono_deleted G H (by intro s hs; exact Finset.mem_union_right E hs)
    hpt

/-- Enlarge the norm-scale target by deleting an additional left-hand spike set `E`. -/
theorem offdiagNormLeSqrtSigma_leftUnion_deleted {ψ : AddChar F ℂ} (G H D E : Finset F)
    (C : ℝ) (hpt : OffdiagNormLeSqrtSigma ψ G H D C) :
    OffdiagNormLeSqrtSigma ψ G H (E ∪ D) C :=
  offdiagNormLeSqrtSigma_mono_deleted G H
    (by intro s hs; exact Finset.mem_union_right E hs) C hpt

/-- Enlarge the exact `sqrt(3)` norm-scale target by deleting an additional left-hand spike set. -/
theorem offdiagNormLeSqrtThreeSigma_leftUnion_deleted {ψ : AddChar F ℂ}
    (G H D E : Finset F) (hpt : OffdiagNormLeSqrtThreeSigma ψ G H D) :
    OffdiagNormLeSqrtThreeSigma ψ G H (E ∪ D) :=
  offdiagNormLeSqrtThreeSigma_mono_deleted G H
    (by intro s hs; exact Finset.mem_union_right E hs) hpt

/-- Enlarge the constant-1 norm-scale target by deleting an additional left-hand spike set. -/
theorem offdiagNormLeSqrtSigmaOne_leftUnion_deleted {ψ : AddChar F ℂ}
    (G H D E : Finset F) (hpt : OffdiagNormLeSqrtSigmaOne ψ G H D) :
    OffdiagNormLeSqrtSigmaOne ψ G H (E ∪ D) :=
  offdiagNormLeSqrtSigmaOne_mono_deleted G H
    (by intro s hs; exact Finset.mem_union_right E hs) hpt

/-- Enlarge the square-root-card target by deleting an additional left-hand spike set. -/
theorem offdiagNormLeSqrtCardMulSup_leftUnion_deleted {ψ : AddChar F ℂ}
    (G H D E : Finset F) (M : ℝ)
    (hpt : OffdiagNormLeSqrtCardMulSup ψ G H D M) :
    OffdiagNormLeSqrtCardMulSup ψ G H (E ∪ D) M :=
  offdiagNormLeSqrtCardMulSup_mono_deleted G H
    (by intro s hs; exact Finset.mem_union_right E hs) M hpt

/-- Enlarge the familiar product-form target by deleting an additional left-hand spike set. -/
theorem offdiagNormLeSqrtCardMulSupProduct_leftUnion_deleted {ψ : AddChar F ℂ}
    (G H D E : Finset F) (M : ℝ)
    (hpt : OffdiagNormLeSqrtCardMulSupProduct ψ G H D M) :
    OffdiagNormLeSqrtCardMulSupProduct ψ G H (E ∪ D) M :=
  offdiagNormLeSqrtCardMulSupProduct_mono_deleted G H
    (by intro s hs; exact Finset.mem_union_right E hs) M hpt

/-- Enlarge the constant product-form target by deleting an additional left-hand spike set. -/
theorem offdiagNormLeConstSqrtCardMulSupProduct_leftUnion_deleted {ψ : AddChar F ℂ}
    (G H D E : Finset F) (C M : ℝ)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    OffdiagNormLeConstSqrtCardMulSupProduct ψ G H (E ∪ D) C M :=
  offdiagNormLeConstSqrtCardMulSupProduct_mono_deleted G H
    (by intro s hs; exact Finset.mem_union_right E hs) C M hpt

/-- Enlarge the `sqrt(3)` product-form target by deleting an additional left-hand spike set. -/
theorem offdiagNormLeSqrtThreeCardMulSupProduct_leftUnion_deleted {ψ : AddChar F ℂ}
    (G H D E : Finset F) (M : ℝ)
    (hpt : OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M) :
    OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H (E ∪ D) M :=
  offdiagNormLeSqrtThreeCardMulSupProduct_mono_deleted G H
    (by intro s hs; exact Finset.mem_union_right E hs) M hpt

/-- **Zeroth rung for the corrected tower, proved.**  At `r = 0`, the away moment simply counts
the non-diagonal offsets, so it is at most `q`; the Wick right-hand side is exactly `q`. -/
theorem wickForIncidenceAwayAt_zero (ψ : AddChar F ℂ) (G H D : Finset F) :
    WickForIncidenceAwayAt ψ G H D 0 := by
  classical
  unfold WickForIncidenceAwayAt incidenceMomentAway
  calc (∑ s₀ ∈ Finset.univ \ D, ‖incidenceSum ψ G H s₀‖ ^ (2 * 0))
      = ((Finset.univ \ D).card : ℝ) := by
        simp
    _ ≤ (Fintype.card F : ℝ) := by
        exact_mod_cast Finset.card_le_univ (Finset.univ \ D)
    _ = (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 0 - 1) : ℝ)
          * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 0 := by
        simp

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

/-- The full corrected tower is reduced to the genuinely hard range `r ≥ 2`: rungs `0` and `1`
are automatic (`r = 1` by the exact second moment). -/
theorem wickForIncidenceAway_of_ge_two {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G H D : Finset F)
    (hhigh : ∀ r : ℕ, 2 ≤ r → WickForIncidenceAwayAt ψ G H D r) :
    WickForIncidenceAway ψ G H D := by
  intro r
  cases r with
  | zero => exact wickForIncidenceAwayAt_zero ψ G H D
  | succ r =>
      cases r with
      | zero => simpa using wickForIncidenceAwayAt_one hψ G H D
      | succ r => exact hhigh (r + 2) (by omega)

/-- **Diagonal-mass cancellation criterion for the corrected tower.**  To prove the
diagonal-subtracted Wick rung, it is enough to prove the raw moment bound with the *entire*
excluded diagonal mass added to the right-hand side:

`S_r ≤ Wick_r + diagonalMass(D)`.

The exact split `S_r = S_r^D + diagonalMass(D)` then cancels the diagonal contribution without any
smallness assumption.  This is the formal workbench hook for future analytic attacks that naturally
estimate the raw expanded moment but isolate the structural diagonal separately. -/
theorem wickForIncidenceAwayAt_of_incidenceMoment_le_wick_add_diag {ψ : AddChar F ℂ}
    (G H D : Finset F) (r : ℕ)
    (hraw :
      incidenceMoment ψ G H r
        ≤ (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
            * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r
          + ∑ s₀ ∈ D, ‖incidenceSum ψ G H s₀‖ ^ (2 * r)) :
    WickForIncidenceAwayAt ψ G H D r := by
  classical
  unfold WickForIncidenceAwayAt
  have hsplit := incidenceMoment_eq_away_add_diag ψ G H D r
  have hdiag_nonneg : 0 ≤ ∑ s₀ ∈ D, ‖incidenceSum ψ G H s₀‖ ^ (2 * r) := by
    positivity
  linarith

/-- Named-Prop form of diagonal-mass cancellation. -/
theorem wickForIncidenceAwayAt_of_rawIncidenceMomentWithDiagonalAt {ψ : AddChar F ℂ}
    (G H D : Finset F) (r : ℕ)
    (hraw : RawIncidenceMomentWithDiagonalAt ψ G H D r) :
    WickForIncidenceAwayAt ψ G H D r :=
  wickForIncidenceAwayAt_of_incidenceMoment_le_wick_add_diag G H D r hraw

/-- **The concrete r=2 target for Round 16.**  To prove the first genuinely open corrected rung,
it is enough to prove the raw fourth-moment estimate with the exact deleted diagonal mass added:

`S₂ ≤ 3 q Σ² + diagonalMass₂(D)`.

This is just the diagonal-mass cancellation criterion specialized to `r = 2`, but it exposes the
right constant (`(2·2-1)‼ = 3`) for probes and future thick-subgroup counting arguments. -/
theorem wickForIncidenceAwayAt_two_of_incidenceMoment_le_three_wick_add_diag {ψ : AddChar F ℂ}
    (G H D : Finset F)
    (hraw :
      incidenceMoment ψ G H 2
        ≤ (Fintype.card F : ℝ) * 3 * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2
          + ∑ s₀ ∈ D, ‖incidenceSum ψ G H s₀‖ ^ 4) :
    WickForIncidenceAwayAt ψ G H D 2 := by
  refine wickForIncidenceAwayAt_of_incidenceMoment_le_wick_add_diag G H D 2 ?_
  have hdf : ((Nat.doubleFactorial (2 * 2 - 1) : ℕ) : ℝ) = 3 := by
    norm_num [Nat.doubleFactorial]
  simpa [hdf] using hraw

/-- **Exact fourth-moment target.**  The first genuinely open corrected rung is equivalent to the
raw fourth-moment estimate

`S₂ ≤ 3 q Σ² + diagonalMass₂(D)`.

This packages the Round-16 target with the constant exposed and no hidden diagonal bookkeeping. -/
theorem wickForIncidenceAwayAt_two_iff_incidenceMoment_le_three_wick_add_diag
    {ψ : AddChar F ℂ} (G H D : Finset F) :
    WickForIncidenceAwayAt ψ G H D 2
      ↔ incidenceMoment ψ G H 2
          ≤ (Fintype.card F : ℝ) * 3 * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2
            + ∑ s₀ ∈ D, ‖incidenceSum ψ G H s₀‖ ^ 4 := by
  constructor
  · intro haway
    unfold WickForIncidenceAwayAt at haway
    rw [incidenceMoment_eq_away_add_diag ψ G H D 2]
    have hdf : ((Nat.doubleFactorial (2 * 2 - 1) : ℕ) : ℝ) = 3 := by
      norm_num [Nat.doubleFactorial]
    simp [hdf] at haway ⊢
    linarith
  · exact wickForIncidenceAwayAt_two_of_incidenceMoment_le_three_wick_add_diag G H D

/-- Named-Prop form of the first hard corrected rung. -/
theorem wickForIncidenceAwayAt_two_iff_rawFourthMomentWithDiagonal
    {ψ : AddChar F ℂ} (G H D : Finset F) :
    WickForIncidenceAwayAt ψ G H D 2 ↔ RawFourthMomentWithDiagonal ψ G H D := by
  simpa [RawFourthMomentWithDiagonal] using
    (wickForIncidenceAwayAt_two_iff_incidenceMoment_le_three_wick_add_diag G H D)

/-- Named-Prop one-way consumer for the first hard corrected rung. -/
theorem wickForIncidenceAwayAt_two_of_rawFourthMomentWithDiagonal {ψ : AddChar F ℂ}
    (G H D : Finset F) (hraw : RawFourthMomentWithDiagonal ψ G H D) :
    WickForIncidenceAwayAt ψ G H D 2 :=
  (wickForIncidenceAwayAt_two_iff_rawFourthMomentWithDiagonal G H D).mpr hraw

/-- **`L∞ × L²` route to the first hard corrected rung.**  If every off-diagonal offset obeys
`‖I_H(s₀)‖² ≤ 3Σ`, where `Σ = ∑_{b∈H} ‖η_b‖²`, then the diagonal-subtracted fourth moment satisfies
the Wick `r = 2` bound `S₂^D ≤ 3 q Σ²`.

This records a second exact entry point to the first open rung: prove a variance-scale pointwise
bound off the diagonal, then combine it with the R13 second moment. -/
theorem wickForIncidenceAwayAt_two_of_offdiag_sq_le_three_sigma {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G H D : Finset F)
    (hpt : ∀ s₀ : F, s₀ ∉ D →
      ‖incidenceSum ψ G H s₀‖ ^ 2 ≤ 3 * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) :
    WickForIncidenceAwayAt ψ G H D 2 := by
  classical
  unfold WickForIncidenceAwayAt incidenceMomentAway
  set Sig : ℝ := ∑ b ∈ H, ‖eta ψ G b‖ ^ 2
  have haway_l2_le_raw :
      (∑ s₀ ∈ Finset.univ \ D, ‖incidenceSum ψ G H s₀‖ ^ 2)
        ≤ ∑ s₀ : F, ‖incidenceSum ψ G H s₀‖ ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro s hs; exact (Finset.mem_sdiff.mp hs).1)
      (by intro s _ _; positivity)
  have haway_l2 :
      (∑ s₀ ∈ Finset.univ \ D, ‖incidenceSum ψ G H s₀‖ ^ 2)
        ≤ (Fintype.card F : ℝ) * Sig := by
    rw [incidenceSum_sq_sum_offsets hψ G H] at haway_l2_le_raw
    simpa [Sig] using haway_l2_le_raw
  have hterm : ∀ s₀ ∈ Finset.univ \ D,
      ‖incidenceSum ψ G H s₀‖ ^ (2 * 2)
        ≤ (3 * Sig) * ‖incidenceSum ψ G H s₀‖ ^ 2 := by
    intro s₀ hs₀
    have hsD : s₀ ∉ D := (Finset.mem_sdiff.mp hs₀).2
    have hpt' : ‖incidenceSum ψ G H s₀‖ ^ 2 ≤ 3 * Sig := by
      simpa [Sig] using hpt s₀ hsD
    have hnonneg : 0 ≤ ‖incidenceSum ψ G H s₀‖ ^ 2 := by positivity
    calc ‖incidenceSum ψ G H s₀‖ ^ (2 * 2)
        = (‖incidenceSum ψ G H s₀‖ ^ 2) * ‖incidenceSum ψ G H s₀‖ ^ 2 := by ring
      _ ≤ (3 * Sig) * ‖incidenceSum ψ G H s₀‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hpt' hnonneg
  have hsum4 :
      (∑ s₀ ∈ Finset.univ \ D, ‖incidenceSum ψ G H s₀‖ ^ (2 * 2))
        ≤ (3 * Sig) * ∑ s₀ ∈ Finset.univ \ D, ‖incidenceSum ψ G H s₀‖ ^ 2 := by
    calc (∑ s₀ ∈ Finset.univ \ D, ‖incidenceSum ψ G H s₀‖ ^ (2 * 2))
        ≤ ∑ s₀ ∈ Finset.univ \ D,
            (3 * Sig) * ‖incidenceSum ψ G H s₀‖ ^ 2 := by
          exact Finset.sum_le_sum hterm
      _ = (3 * Sig) * ∑ s₀ ∈ Finset.univ \ D, ‖incidenceSum ψ G H s₀‖ ^ 2 := by
          rw [← Finset.mul_sum]
  have hcoef_nonneg : 0 ≤ 3 * Sig := by
    dsimp [Sig]
    positivity
  have hsum2 :
      (3 * Sig) * (∑ s₀ ∈ Finset.univ \ D, ‖incidenceSum ψ G H s₀‖ ^ 2)
        ≤ (3 * Sig) * ((Fintype.card F : ℝ) * Sig) :=
    mul_le_mul_of_nonneg_left haway_l2 hcoef_nonneg
  have hdf : ((Nat.doubleFactorial (2 * 2 - 1) : ℕ) : ℝ) = 3 := by
    norm_num [Nat.doubleFactorial]
  calc (∑ s₀ ∈ Finset.univ \ D, ‖incidenceSum ψ G H s₀‖ ^ (2 * 2))
      ≤ (3 * Sig) * ((Fintype.card F : ℝ) * Sig) := le_trans hsum4 hsum2
    _ = (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 2 - 1) : ℝ) * Sig ^ 2 := by
        rw [hdf]
        ring

/-- Named-target version of the `L∞ × L²` route.  The same off-diagonal square bound proves the
packaged raw fourth-moment-with-diagonal target. -/
theorem rawFourthMomentWithDiagonal_of_offdiag_sq_le_three_sigma {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G H D : Finset F)
    (hpt : ∀ s₀ : F, s₀ ∉ D →
      ‖incidenceSum ψ G H s₀‖ ^ 2 ≤ 3 * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) :
    RawFourthMomentWithDiagonal ψ G H D :=
  (wickForIncidenceAwayAt_two_iff_rawFourthMomentWithDiagonal G H D).mp
    (wickForIncidenceAwayAt_two_of_offdiag_sq_le_three_sigma hψ G H D hpt)

/-- Named-Prop version of the `L∞ × L²` route to away-Wick at `r = 2`. -/
theorem wickForIncidenceAwayAt_two_of_offdiagSquareLeThreeSigma {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G H D : Finset F)
    (hpt : OffdiagSquareLeThreeSigma ψ G H D) :
    WickForIncidenceAwayAt ψ G H D 2 :=
  wickForIncidenceAwayAt_two_of_offdiag_sq_le_three_sigma hψ G H D hpt

/-- Named-Prop version of the `L∞ × L²` route to the raw fourth-moment target. -/
theorem rawFourthMomentWithDiagonal_of_offdiagSquareLeThreeSigma {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G H D : Finset F)
    (hpt : OffdiagSquareLeThreeSigma ψ G H D) :
    RawFourthMomentWithDiagonal ψ G H D :=
  rawFourthMomentWithDiagonal_of_offdiag_sq_le_three_sigma hψ G H D hpt

/-- Pointwise square control off `D` proves away-Wick at `r = 2` after deleting any extra spike
set `E`. -/
theorem wickForIncidenceAwayAt_two_union_deleted_of_offdiagSquareLeThreeSigma
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F)
    (hpt : OffdiagSquareLeThreeSigma ψ G H D) :
    WickForIncidenceAwayAt ψ G H (D ∪ E) 2 :=
  wickForIncidenceAwayAt_two_of_offdiagSquareLeThreeSigma hψ G H (D ∪ E)
    (offdiagSquareLeThreeSigma_union_deleted G H D E hpt)

/-- Pointwise square control off `D` proves the raw fourth target after deleting any extra spike
set `E`. -/
theorem rawFourthMomentWithDiagonal_union_deleted_of_offdiagSquareLeThreeSigma
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F)
    (hpt : OffdiagSquareLeThreeSigma ψ G H D) :
    RawFourthMomentWithDiagonal ψ G H (D ∪ E) :=
  rawFourthMomentWithDiagonal_of_offdiagSquareLeThreeSigma hψ G H (D ∪ E)
    (offdiagSquareLeThreeSigma_union_deleted G H D E hpt)

/-- Pointwise square control off `D` proves away-Wick at `r = 2` after deleting an extra left-hand
spike set `E`. -/
theorem wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagSquareLeThreeSigma
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F)
    (hpt : OffdiagSquareLeThreeSigma ψ G H D) :
    WickForIncidenceAwayAt ψ G H (E ∪ D) 2 :=
  wickForIncidenceAwayAt_two_of_offdiagSquareLeThreeSigma hψ G H (E ∪ D)
    (offdiagSquareLeThreeSigma_leftUnion_deleted G H D E hpt)

/-- Pointwise square control off `D` proves the raw fourth target after deleting an extra left-hand
spike set `E`. -/
theorem rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagSquareLeThreeSigma
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F)
    (hpt : OffdiagSquareLeThreeSigma ψ G H D) :
    RawFourthMomentWithDiagonal ψ G H (E ∪ D) :=
  rawFourthMomentWithDiagonal_of_offdiagSquareLeThreeSigma hψ G H (E ∪ D)
    (offdiagSquareLeThreeSigma_leftUnion_deleted G H D E hpt)

/-- Norm-scale off-diagonal control implies the squared `3Σ` target whenever `C² ≤ 3`. -/
theorem offdiagSquareLeThreeSigma_of_offdiagNormLeSqrtSigma {ψ : AddChar F ℂ}
    (G H D : Finset F) {C : ℝ} (hC0 : 0 ≤ C) (hC : C ^ 2 ≤ 3)
    (hpt : OffdiagNormLeSqrtSigma ψ G H D C) :
    OffdiagSquareLeThreeSigma ψ G H D := by
  intro s₀ hs₀
  set Sig : ℝ := ∑ b ∈ H, ‖eta ψ G b‖ ^ 2
  have hSig0 : 0 ≤ Sig := by
    dsimp [Sig]
    positivity
  have hnorm := hpt s₀ hs₀
  have hright_nonneg : 0 ≤ C * Real.sqrt Sig := mul_nonneg hC0 (Real.sqrt_nonneg Sig)
  have hsq : ‖incidenceSum ψ G H s₀‖ ^ 2 ≤ (C * Real.sqrt Sig) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have htarget : (C * Real.sqrt Sig) ^ 2 ≤ 3 * Sig := by
    calc (C * Real.sqrt Sig) ^ 2
        = C ^ 2 * Sig := by rw [mul_pow, Real.sq_sqrt hSig0]
      _ ≤ 3 * Sig := mul_le_mul_of_nonneg_right hC hSig0
  exact le_trans hsq htarget

/-- Norm-scale off-diagonal control gives away-Wick at the first hard rung. -/
theorem wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtSigma {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G H D : Finset F) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : C ^ 2 ≤ 3)
    (hpt : OffdiagNormLeSqrtSigma ψ G H D C) :
    WickForIncidenceAwayAt ψ G H D 2 :=
  wickForIncidenceAwayAt_two_of_offdiagSquareLeThreeSigma hψ G H D
    (offdiagSquareLeThreeSigma_of_offdiagNormLeSqrtSigma G H D hC0 hC hpt)

/-- Norm-scale off-diagonal control gives the named raw fourth-moment target. -/
theorem rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtSigma {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G H D : Finset F) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : C ^ 2 ≤ 3)
    (hpt : OffdiagNormLeSqrtSigma ψ G H D C) :
    RawFourthMomentWithDiagonal ψ G H D :=
  rawFourthMomentWithDiagonal_of_offdiagSquareLeThreeSigma hψ G H D
    (offdiagSquareLeThreeSigma_of_offdiagNormLeSqrtSigma G H D hC0 hC hpt)

/-- The exact-constant norm-scale target implies the squared `3Σ` target. -/
theorem offdiagSquareLeThreeSigma_of_offdiagNormLeSqrtThreeSigma {ψ : AddChar F ℂ}
    (G H D : Finset F) (hpt : OffdiagNormLeSqrtThreeSigma ψ G H D) :
    OffdiagSquareLeThreeSigma ψ G H D := by
  refine offdiagSquareLeThreeSigma_of_offdiagNormLeSqrtSigma G H D
    (Real.sqrt_nonneg 3) ?_ hpt
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

/-- Exact-constant norm-scale control gives away-Wick at the first hard rung. -/
theorem wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtThreeSigma {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G H D : Finset F)
    (hpt : OffdiagNormLeSqrtThreeSigma ψ G H D) :
    WickForIncidenceAwayAt ψ G H D 2 :=
  wickForIncidenceAwayAt_two_of_offdiagSquareLeThreeSigma hψ G H D
    (offdiagSquareLeThreeSigma_of_offdiagNormLeSqrtThreeSigma G H D hpt)

/-- Exact-constant norm-scale control gives the named raw fourth-moment target. -/
theorem rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtThreeSigma {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G H D : Finset F)
    (hpt : OffdiagNormLeSqrtThreeSigma ψ G H D) :
    RawFourthMomentWithDiagonal ψ G H D :=
  rawFourthMomentWithDiagonal_of_offdiagSquareLeThreeSigma hψ G H D
    (offdiagSquareLeThreeSigma_of_offdiagNormLeSqrtThreeSigma G H D hpt)

/-- Exact `sqrt(3)` norm-scale control off `D` proves away-Wick at `r = 2` after deleting any
extra spike set `E`. -/
theorem wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtThreeSigma
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F)
    (hpt : OffdiagNormLeSqrtThreeSigma ψ G H D) :
    WickForIncidenceAwayAt ψ G H (D ∪ E) 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtThreeSigma hψ G H (D ∪ E)
    (offdiagNormLeSqrtThreeSigma_union_deleted G H D E hpt)

/-- Exact `sqrt(3)` norm-scale control off `D` proves the raw fourth target after deleting any
extra spike set `E`. -/
theorem rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtThreeSigma
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F)
    (hpt : OffdiagNormLeSqrtThreeSigma ψ G H D) :
    RawFourthMomentWithDiagonal ψ G H (D ∪ E) :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtThreeSigma hψ G H (D ∪ E)
    (offdiagNormLeSqrtThreeSigma_union_deleted G H D E hpt)

/-- Exact `sqrt(3)` norm-scale control off `D` proves away-Wick at `r = 2` after deleting an extra
left-hand spike set `E`. -/
theorem wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtThreeSigma
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F)
    (hpt : OffdiagNormLeSqrtThreeSigma ψ G H D) :
    WickForIncidenceAwayAt ψ G H (E ∪ D) 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtThreeSigma hψ G H (E ∪ D)
    (offdiagNormLeSqrtThreeSigma_leftUnion_deleted G H D E hpt)

/-- Exact `sqrt(3)` norm-scale control off `D` proves the raw fourth target after deleting an extra
left-hand spike set `E`. -/
theorem rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtThreeSigma
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F)
    (hpt : OffdiagNormLeSqrtThreeSigma ψ G H D) :
    RawFourthMomentWithDiagonal ψ G H (E ∪ D) :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtThreeSigma hψ G H (E ∪ D)
    (offdiagNormLeSqrtThreeSigma_leftUnion_deleted G H D E hpt)

/-- A norm-scale off-diagonal bound with any constant `C ≤ sqrt(3)` gives away-Wick at `r = 2`. -/
theorem wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtSigma_le_sqrtThree
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {C : ℝ}
    (hC : C ≤ Real.sqrt 3) (hpt : OffdiagNormLeSqrtSigma ψ G H D C) :
    WickForIncidenceAwayAt ψ G H D 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtThreeSigma hψ G H D
    (offdiagNormLeSqrtThreeSigma_of_offdiagNormLeSqrtSigma_le G H D hC hpt)

/-- A norm-scale off-diagonal bound with any constant `C ≤ sqrt(3)` gives the raw fourth target. -/
theorem rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtSigma_le_sqrtThree
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {C : ℝ}
    (hC : C ≤ Real.sqrt 3) (hpt : OffdiagNormLeSqrtSigma ψ G H D C) :
    RawFourthMomentWithDiagonal ψ G H D :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtThreeSigma hψ G H D
    (offdiagNormLeSqrtThreeSigma_of_offdiagNormLeSqrtSigma_le G H D hC hpt)

/-- A norm-scale off-diagonal bound with any `C ≤ sqrt(3)` proves away-Wick at `r = 2` after
deleting any extra spike set `E`. -/
theorem wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtSigma_le_sqrtThree
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {C : ℝ}
    (hC : C ≤ Real.sqrt 3) (hpt : OffdiagNormLeSqrtSigma ψ G H D C) :
    WickForIncidenceAwayAt ψ G H (D ∪ E) 2 :=
  wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtThreeSigma hψ G H D E
    (offdiagNormLeSqrtThreeSigma_of_offdiagNormLeSqrtSigma_le G H D hC hpt)

/-- A norm-scale off-diagonal bound with any `C ≤ sqrt(3)` proves the raw fourth target after
deleting any extra spike set `E`. -/
theorem rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtSigma_le_sqrtThree
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {C : ℝ}
    (hC : C ≤ Real.sqrt 3) (hpt : OffdiagNormLeSqrtSigma ψ G H D C) :
    RawFourthMomentWithDiagonal ψ G H (D ∪ E) :=
  rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtThreeSigma hψ G H D E
    (offdiagNormLeSqrtThreeSigma_of_offdiagNormLeSqrtSigma_le G H D hC hpt)

/-- A norm-scale off-diagonal bound with any `C ≤ sqrt(3)` proves away-Wick at `r = 2` after
deleting an extra left-hand spike set `E`. -/
theorem wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtSigma_le_sqrtThree
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {C : ℝ}
    (hC : C ≤ Real.sqrt 3) (hpt : OffdiagNormLeSqrtSigma ψ G H D C) :
    WickForIncidenceAwayAt ψ G H (E ∪ D) 2 :=
  wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtThreeSigma hψ G H D E
    (offdiagNormLeSqrtThreeSigma_of_offdiagNormLeSqrtSigma_le G H D hC hpt)

/-- A norm-scale off-diagonal bound with any `C ≤ sqrt(3)` proves the raw fourth target after
deleting an extra left-hand spike set `E`. -/
theorem rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtSigma_le_sqrtThree
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {C : ℝ}
    (hC : C ≤ Real.sqrt 3) (hpt : OffdiagNormLeSqrtSigma ψ G H D C) :
    RawFourthMomentWithDiagonal ψ G H (E ∪ D) :=
  rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtThreeSigma hψ G H D E
    (offdiagNormLeSqrtThreeSigma_of_offdiagNormLeSqrtSigma_le G H D hC hpt)

/-- Constant-1 off-diagonal norm control gives away-Wick at the first hard rung. -/
theorem wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtSigmaOne
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F)
    (hpt : OffdiagNormLeSqrtSigmaOne ψ G H D) :
    WickForIncidenceAwayAt ψ G H D 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtThreeSigma hψ G H D
    (offdiagNormLeSqrtThreeSigma_of_offdiagNormLeSqrtSigmaOne G H D hpt)

/-- Constant-1 off-diagonal norm control gives the named raw fourth-moment target. -/
theorem rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtSigmaOne
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F)
    (hpt : OffdiagNormLeSqrtSigmaOne ψ G H D) :
    RawFourthMomentWithDiagonal ψ G H D :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtThreeSigma hψ G H D
    (offdiagNormLeSqrtThreeSigma_of_offdiagNormLeSqrtSigmaOne G H D hpt)

/-- Constant-1 norm-scale control off `D` proves away-Wick at `r = 2` after deleting any extra
spike set `E`. -/
theorem wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtSigmaOne
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F)
    (hpt : OffdiagNormLeSqrtSigmaOne ψ G H D) :
    WickForIncidenceAwayAt ψ G H (D ∪ E) 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtSigmaOne hψ G H (D ∪ E)
    (offdiagNormLeSqrtSigmaOne_union_deleted G H D E hpt)

/-- Constant-1 norm-scale control off `D` proves the raw fourth target after deleting any extra
spike set `E`. -/
theorem rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtSigmaOne
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F)
    (hpt : OffdiagNormLeSqrtSigmaOne ψ G H D) :
    RawFourthMomentWithDiagonal ψ G H (D ∪ E) :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtSigmaOne hψ G H (D ∪ E)
    (offdiagNormLeSqrtSigmaOne_union_deleted G H D E hpt)

/-- Constant-1 norm-scale control off `D` proves away-Wick at `r = 2` after deleting an extra
left-hand spike set `E`. -/
theorem wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtSigmaOne
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F)
    (hpt : OffdiagNormLeSqrtSigmaOne ψ G H D) :
    WickForIncidenceAwayAt ψ G H (E ∪ D) 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtSigmaOne hψ G H (E ∪ D)
    (offdiagNormLeSqrtSigmaOne_leftUnion_deleted G H D E hpt)

/-- Constant-1 norm-scale control off `D` proves the raw fourth target after deleting an extra
left-hand spike set `E`. -/
theorem rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtSigmaOne
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F)
    (hpt : OffdiagNormLeSqrtSigmaOne ψ G H D) :
    RawFourthMomentWithDiagonal ψ G H (E ∪ D) :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtSigmaOne hψ G H (E ∪ D)
    (offdiagNormLeSqrtSigmaOne_leftUnion_deleted G H D E hpt)

/-- Energy-normalized off-diagonal control plus a coefficient sup bound gives the familiar
`sqrt(|H|·M²)` Problem-B scale. -/
theorem offdiagNormLeSqrtCardMulSup_of_offdiagNormLeSqrtSigmaOne
    {ψ : AddChar F ℂ} (G H D : Finset F) {M : ℝ}
    (hM : ∀ b ∈ H, ‖eta ψ G b‖ ≤ M)
    (hpt : OffdiagNormLeSqrtSigmaOne ψ G H D) :
    OffdiagNormLeSqrtCardMulSup ψ G H D M := by
  intro s₀ hs₀
  have hpt' : ‖incidenceSum ψ G H s₀‖
      ≤ Real.sqrt (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) := by
    simpa [OffdiagNormLeSqrtSigmaOne, OffdiagNormLeSqrtSigma] using hpt s₀ hs₀
  refine le_trans hpt' ?_
  have hsum : (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ≤ (H.card : ℝ) * M ^ 2 := by
    calc (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
        ≤ ∑ _b ∈ H, M ^ 2 := by
          refine Finset.sum_le_sum (fun b hb => ?_)
          have h1 : ‖eta ψ G b‖ ≤ M := hM b hb
          have h0 : 0 ≤ ‖eta ψ G b‖ := norm_nonneg _
          nlinarith [h1, h0]
      _ = (H.card : ℝ) * M ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  exact Real.sqrt_le_sqrt hsum

/-- A coefficient lower bound gives the energy-lower hypothesis
`|H| · m² ≤ Σ`.  This is the dual of the sup-envelope estimate used to pass from variance-scale
control to product-form control. -/
theorem card_mul_sq_le_energy_of_coeff_lower_bound
    {ψ : AddChar F ℂ} (G H : Finset F) {m : ℝ}
    (hm0 : 0 ≤ m)
    (hm : ∀ b ∈ H, m ≤ ‖eta ψ G b‖) :
    (H.card : ℝ) * m ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 := by
  calc (H.card : ℝ) * m ^ 2
      = ∑ _b ∈ H, m ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 := by
        refine Finset.sum_le_sum (fun b hb => ?_)
        have h0 : 0 ≤ ‖eta ψ G b‖ := norm_nonneg _
        nlinarith [hm0, hm b hb, h0]

/-- If every coefficient on `H` has norm exactly `m`, then the coefficient energy is exactly
`|H| · m²`. -/
theorem energy_eq_card_mul_sq_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (G H : Finset F) {m : ℝ}
    (hm : ∀ b ∈ H, ‖eta ψ G b‖ = m) :
    (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) = (H.card : ℝ) * m ^ 2 := by
  calc (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
      = ∑ _b ∈ H, m ^ 2 := by
          refine Finset.sum_congr rfl (fun b hb => ?_)
          rw [hm b hb]
    _ = (H.card : ℝ) * m ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Exact coefficient norms give the energy-lower hypothesis. -/
theorem card_mul_sq_le_energy_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (G H : Finset F) {m : ℝ}
    (hm : ∀ b ∈ H, ‖eta ψ G b‖ = m) :
    (H.card : ℝ) * m ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 := by
  rw [energy_eq_card_mul_sq_of_coeff_norm_eq G H hm]

/-- Convert `sqrt(|H|·M²)` to the familiar `sqrt(|H|)·M` product form when `M ≥ 0`. -/
theorem offdiagNormLeSqrtCardMulSupProduct_of_sqrtCardMulSup
    {ψ : AddChar F ℂ} (G H D : Finset F) {M : ℝ} (hM0 : 0 ≤ M)
    (hpt : OffdiagNormLeSqrtCardMulSup ψ G H D M) :
    OffdiagNormLeSqrtCardMulSupProduct ψ G H D M := by
  intro s₀ hs₀
  refine le_trans (hpt s₀ hs₀) ?_
  have hcard_nonneg : 0 ≤ (H.card : ℝ) := by positivity
  rw [Real.sqrt_mul hcard_nonneg, Real.sqrt_sq hM0]

/-- Energy-normalized constant-1 off-diagonal control plus a coefficient sup bound gives the
familiar `sqrt(|H|)·M` Problem-B scale. -/
theorem offdiagNormLeSqrtCardMulSupProduct_of_offdiagNormLeSqrtSigmaOne
    {ψ : AddChar F ℂ} (G H D : Finset F) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ b ∈ H, ‖eta ψ G b‖ ≤ M)
    (hpt : OffdiagNormLeSqrtSigmaOne ψ G H D) :
    OffdiagNormLeSqrtCardMulSupProduct ψ G H D M :=
  offdiagNormLeSqrtCardMulSupProduct_of_sqrtCardMulSup G H D hM0
    (offdiagNormLeSqrtCardMulSup_of_offdiagNormLeSqrtSigmaOne G H D hM hpt)

/-- Energy-normalized constant-`C` off-diagonal control plus a coefficient sup bound gives the
familiar `C·sqrt(|H|)·M` Problem-B scale. -/
theorem offdiagNormLeConstSqrtCardMulSupProduct_of_offdiagNormLeSqrtSigma
    {ψ : AddChar F ℂ} (G H D : Finset F) {C M : ℝ} (hC0 : 0 ≤ C) (hM0 : 0 ≤ M)
    (hM : ∀ b ∈ H, ‖eta ψ G b‖ ≤ M)
    (hpt : OffdiagNormLeSqrtSigma ψ G H D C) :
    OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M := by
  intro s₀ hs₀
  have hsum : (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ≤ (H.card : ℝ) * M ^ 2 := by
    calc (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
        ≤ ∑ _b ∈ H, M ^ 2 := by
          refine Finset.sum_le_sum (fun b hb => ?_)
          have h1 : ‖eta ψ G b‖ ≤ M := hM b hb
          have h0 : 0 ≤ ‖eta ψ G b‖ := norm_nonneg _
          nlinarith [h1, h0]
      _ = (H.card : ℝ) * M ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hsqrt : Real.sqrt (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
      ≤ Real.sqrt (H.card : ℝ) * M := by
    refine le_trans (Real.sqrt_le_sqrt hsum) ?_
    have hcard_nonneg : 0 ≤ (H.card : ℝ) := by positivity
    rw [Real.sqrt_mul hcard_nonneg, Real.sqrt_sq hM0]
  calc ‖incidenceSum ψ G H s₀‖
      ≤ C * Real.sqrt (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) := hpt s₀ hs₀
    _ ≤ C * (Real.sqrt (H.card : ℝ) * M) :=
        mul_le_mul_of_nonneg_left hsqrt hC0

/-- Constant-1 product form as the `C = 1` specialization of the generic product target. -/
theorem offdiagNormLeConstSqrtCardMulSupProduct_one_of_product
    {ψ : AddChar F ℂ} (G H D : Finset F) (M : ℝ)
    (hpt : OffdiagNormLeSqrtCardMulSupProduct ψ G H D M) :
    OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D 1 M := by
  intro s₀ hs₀
  simpa using hpt s₀ hs₀

/-- Monotonicity of the familiar product-form target in the explicit constant. -/
theorem offdiagNormLeConstSqrtCardMulSupProduct_mono_const
    {ψ : AddChar F ℂ} (G H D : Finset F) {C C' M : ℝ} (hCC' : C ≤ C')
    (hM0 : 0 ≤ M)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C' M := by
  intro s₀ hs₀
  refine le_trans (hpt s₀ hs₀) ?_
  exact mul_le_mul_of_nonneg_right hCC'
    (mul_nonneg (Real.sqrt_nonneg (H.card : ℝ)) hM0)

/-- The constant-1 product form implies the named `sqrt(3)` product form. -/
theorem offdiagNormLeSqrtThreeCardMulSupProduct_of_offdiagNormLeSqrtCardMulSupProduct
    {ψ : AddChar F ℂ} (G H D : Finset F) {M : ℝ} (hM0 : 0 ≤ M)
    (hpt : OffdiagNormLeSqrtCardMulSupProduct ψ G H D M) :
    OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M := by
  have h1sqrt3 : (1 : ℝ) ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]
  exact offdiagNormLeConstSqrtCardMulSupProduct_mono_const G H D h1sqrt3 hM0
    (offdiagNormLeConstSqrtCardMulSupProduct_one_of_product G H D M hpt)

/-- The constant-1 product form implies any larger-constant product form. -/
theorem offdiagNormLeConstSqrtCardMulSupProduct_of_product
    {ψ : AddChar F ℂ} (G H D : Finset F) {C M : ℝ} (hC : 1 ≤ C) (hM0 : 0 ≤ M)
    (hpt : OffdiagNormLeSqrtCardMulSupProduct ψ G H D M) :
    OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M :=
  offdiagNormLeConstSqrtCardMulSupProduct_mono_const G H D hC hM0
    (offdiagNormLeConstSqrtCardMulSupProduct_one_of_product G H D M hpt)

/-- The square-root-card scale implies any larger-constant product form when `M ≥ 0`. -/
theorem offdiagNormLeConstSqrtCardMulSupProduct_of_sqrtCardMulSup
    {ψ : AddChar F ℂ} (G H D : Finset F) {C M : ℝ} (hC : 1 ≤ C) (hM0 : 0 ≤ M)
    (hpt : OffdiagNormLeSqrtCardMulSup ψ G H D M) :
    OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M :=
  offdiagNormLeConstSqrtCardMulSupProduct_of_product G H D hC hM0
    (offdiagNormLeSqrtCardMulSupProduct_of_sqrtCardMulSup G H D hM0 hpt)

/-- Energy-normalized constant-1 off-diagonal control plus a coefficient sup bound gives the
`sqrt(3)` familiar product scale. -/
theorem offdiagNormLeSqrtThreeCardMulSupProduct_of_offdiagNormLeSqrtSigmaOne
    {ψ : AddChar F ℂ} (G H D : Finset F) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ b ∈ H, ‖eta ψ G b‖ ≤ M)
    (hpt : OffdiagNormLeSqrtSigmaOne ψ G H D) :
    OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M :=
  offdiagNormLeSqrtThreeCardMulSupProduct_of_offdiagNormLeSqrtCardMulSupProduct G H D hM0
    (offdiagNormLeSqrtCardMulSupProduct_of_offdiagNormLeSqrtSigmaOne G H D hM0 hM hpt)

/-- `sqrt(3)` energy-normalized control plus a coefficient sup bound gives the `sqrt(3)` familiar
product scale. -/
theorem offdiagNormLeSqrtThreeCardMulSupProduct_of_offdiagNormLeSqrtThreeSigma
    {ψ : AddChar F ℂ} (G H D : Finset F) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ b ∈ H, ‖eta ψ G b‖ ≤ M)
    (hpt : OffdiagNormLeSqrtThreeSigma ψ G H D) :
    OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M :=
  offdiagNormLeConstSqrtCardMulSupProduct_of_offdiagNormLeSqrtSigma
    G H D (Real.sqrt_nonneg 3) hM0 hM hpt

/-- Constant product-form control implies variance-scale control when `C ≤ C'` and the sup
envelope does not exceed the actual coefficient energy: `|H|·M² ≤ Σ`. -/
theorem offdiagNormLeSqrtSigma_of_offdiagNormLeConstSqrtCardMulSupProduct
    {ψ : AddChar F ℂ} (G H D : Finset F) {C C' M : ℝ}
    (hCC' : C ≤ C') (hC0 : 0 ≤ C') (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    OffdiagNormLeSqrtSigma ψ G H D C' := by
  intro s₀ hs₀
  refine le_trans (hpt s₀ hs₀) ?_
  have hcard_nonneg : 0 ≤ (H.card : ℝ) := by positivity
  have hscale :
      Real.sqrt (H.card : ℝ) * M
        ≤ Real.sqrt (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) := by
    calc Real.sqrt (H.card : ℝ) * M
        = Real.sqrt ((H.card : ℝ) * M ^ 2) := by
            rw [Real.sqrt_mul hcard_nonneg, Real.sqrt_sq hM0]
      _ ≤ Real.sqrt (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) := Real.sqrt_le_sqrt henergy
  calc C * (Real.sqrt (H.card : ℝ) * M)
      ≤ C' * (Real.sqrt (H.card : ℝ) * M) :=
        mul_le_mul_of_nonneg_right hCC' (mul_nonneg (Real.sqrt_nonneg (H.card : ℝ)) hM0)
    _ ≤ C' * Real.sqrt (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hscale hC0

/-- Constant product-form control with `C ≤ sqrt(3)` implies the exact `sqrt(3)` variance-scale
target under the energy-lower hypothesis. -/
theorem offdiagNormLeSqrtThreeSigma_of_offdiagNormLeConstSqrtCardMulSupProduct
    {ψ : AddChar F ℂ} (G H D : Finset F) {C M : ℝ}
    (hC : C ≤ Real.sqrt 3) (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    OffdiagNormLeSqrtThreeSigma ψ G H D :=
  offdiagNormLeSqrtSigma_of_offdiagNormLeConstSqrtCardMulSupProduct G H D hC
    (Real.sqrt_nonneg 3) hM0 henergy hpt

/-- Constant product-form control with `C ≤ sqrt(3)` plus the energy-lower hypothesis proves
away-Wick at `r = 2`. -/
theorem wickForIncidenceAwayAt_two_of_offdiagNormLeConstSqrtCardMulSupProduct
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {C M : ℝ}
    (hC : C ≤ Real.sqrt 3) (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    WickForIncidenceAwayAt ψ G H D 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtThreeSigma hψ G H D
    (offdiagNormLeSqrtThreeSigma_of_offdiagNormLeConstSqrtCardMulSupProduct G H D hC
      hM0 henergy hpt)

/-- Constant product-form control with `C ≤ sqrt(3)` plus the energy-lower hypothesis proves the
raw fourth target. -/
theorem rawFourthMomentWithDiagonal_of_offdiagNormLeConstSqrtCardMulSupProduct
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {C M : ℝ}
    (hC : C ≤ Real.sqrt 3) (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    RawFourthMomentWithDiagonal ψ G H D :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtThreeSigma hψ G H D
    (offdiagNormLeSqrtThreeSigma_of_offdiagNormLeConstSqrtCardMulSupProduct G H D hC
      hM0 henergy hpt)

/-- Constant product-form control with `C ≤ sqrt(3)` plus the energy-lower hypothesis proves
away-Wick at `r = 2` after deleting an additional spike set `E`. -/
theorem wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {C M : ℝ}
    (hC : C ≤ Real.sqrt 3) (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    WickForIncidenceAwayAt ψ G H (D ∪ E) 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeConstSqrtCardMulSupProduct hψ G H (D ∪ E)
    hC hM0 henergy
    (offdiagNormLeConstSqrtCardMulSupProduct_mono_deleted G H
      (by intro s hs; exact Finset.mem_union_left E hs) C M hpt)

/-- Constant product-form control with `C ≤ sqrt(3)` plus the energy-lower hypothesis proves the
raw fourth target after deleting an additional spike set `E`. -/
theorem rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {C M : ℝ}
    (hC : C ≤ Real.sqrt 3) (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    RawFourthMomentWithDiagonal ψ G H (D ∪ E) :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeConstSqrtCardMulSupProduct hψ G H (D ∪ E)
    hC hM0 henergy
    (offdiagNormLeConstSqrtCardMulSupProduct_mono_deleted G H
      (by intro s hs; exact Finset.mem_union_left E hs) C M hpt)

/-- Constant product-form control with `C ≤ sqrt(3)` plus the energy-lower hypothesis proves
away-Wick at `r = 2` after deleting an additional left-hand spike set `E`. -/
theorem wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {C M : ℝ}
    (hC : C ≤ Real.sqrt 3) (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    WickForIncidenceAwayAt ψ G H (E ∪ D) 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeConstSqrtCardMulSupProduct hψ G H (E ∪ D)
    hC hM0 henergy
    (offdiagNormLeConstSqrtCardMulSupProduct_mono_deleted G H
      (by intro s hs; exact Finset.mem_union_right E hs) C M hpt)

/-- Constant product-form control with `C ≤ sqrt(3)` plus the energy-lower hypothesis proves the
raw fourth target after deleting an additional left-hand spike set `E`. -/
theorem rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {C M : ℝ}
    (hC : C ≤ Real.sqrt 3) (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    RawFourthMomentWithDiagonal ψ G H (E ∪ D) :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeConstSqrtCardMulSupProduct hψ G H (E ∪ D)
    hC hM0 henergy
    (offdiagNormLeConstSqrtCardMulSupProduct_mono_deleted G H
      (by intro s hs; exact Finset.mem_union_right E hs) C M hpt)

/-- Constant product-form control with a matching coefficient lower bound implies variance-scale
control.  The lower bound discharges the energy-lower hypothesis. -/
theorem offdiagNormLeSqrtSigma_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_lower
    {ψ : AddChar F ℂ} (G H D : Finset F) {C C' M : ℝ}
    (hCC' : C ≤ C') (hC0 : 0 ≤ C') (hM0 : 0 ≤ M)
    (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    OffdiagNormLeSqrtSigma ψ G H D C' :=
  offdiagNormLeSqrtSigma_of_offdiagNormLeConstSqrtCardMulSupProduct G H D hCC'
    hC0 hM0 (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Constant product-form control with `C ≤ sqrt(3)` and a matching coefficient lower bound
implies the exact `sqrt(3)` variance-scale target. -/
theorem offdiagNormLeSqrtThreeSigma_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_lower
    {ψ : AddChar F ℂ} (G H D : Finset F) {C M : ℝ}
    (hC : C ≤ Real.sqrt 3) (hM0 : 0 ≤ M)
    (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    OffdiagNormLeSqrtThreeSigma ψ G H D :=
  offdiagNormLeSqrtThreeSigma_of_offdiagNormLeConstSqrtCardMulSupProduct G H D hC
    hM0 (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Constant product-form control with exact coefficient norms implies variance-scale control. -/
theorem offdiagNormLeSqrtSigma_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (G H D : Finset F) {C C' M : ℝ}
    (hCC' : C ≤ C') (hC0 : 0 ≤ C') (hM0 : 0 ≤ M)
    (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    OffdiagNormLeSqrtSigma ψ G H D C' :=
  offdiagNormLeSqrtSigma_of_offdiagNormLeConstSqrtCardMulSupProduct G H D hCC'
    hC0 hM0 (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Constant product-form control with `C ≤ sqrt(3)` and exact coefficient norms implies the exact
`sqrt(3)` variance-scale target. -/
theorem offdiagNormLeSqrtThreeSigma_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (G H D : Finset F) {C M : ℝ}
    (hC : C ≤ Real.sqrt 3) (hM0 : 0 ≤ M)
    (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    OffdiagNormLeSqrtThreeSigma ψ G H D :=
  offdiagNormLeSqrtThreeSigma_of_offdiagNormLeConstSqrtCardMulSupProduct G H D hC
    hM0 (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Constant product-form control with exact coefficient norms proves away-Wick at `r = 2`. -/
theorem wickForIncidenceAwayAt_two_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {C M : ℝ}
    (hC : C ≤ Real.sqrt 3) (hM0 : 0 ≤ M)
    (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    WickForIncidenceAwayAt ψ G H D 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeConstSqrtCardMulSupProduct hψ G H D
    hC hM0 (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Constant product-form control with exact coefficient norms proves the raw fourth target. -/
theorem rawFourthMomentWithDiagonal_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {C M : ℝ}
    (hC : C ≤ Real.sqrt 3) (hM0 : 0 ≤ M)
    (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    RawFourthMomentWithDiagonal ψ G H D :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeConstSqrtCardMulSupProduct hψ G H D
    hC hM0 (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Constant product-form control with exact coefficient norms proves away-Wick at `r = 2` after
deleting an additional spike set `E`. -/
theorem wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {C M : ℝ}
    (hC : C ≤ Real.sqrt 3) (hM0 : 0 ≤ M)
    (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    WickForIncidenceAwayAt ψ G H (D ∪ E) 2 :=
  wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct hψ G H D E
    hC hM0 (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Constant product-form control with exact coefficient norms proves the raw fourth target after
deleting an additional spike set `E`. -/
theorem rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {C M : ℝ}
    (hC : C ≤ Real.sqrt 3) (hM0 : 0 ≤ M)
    (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    RawFourthMomentWithDiagonal ψ G H (D ∪ E) :=
  rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct hψ G H D E
    hC hM0 (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Constant product-form control with exact coefficient norms proves away-Wick at `r = 2` after
deleting an additional left-hand spike set `E`. -/
theorem wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {C M : ℝ}
    (hC : C ≤ Real.sqrt 3) (hM0 : 0 ≤ M)
    (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    WickForIncidenceAwayAt ψ G H (E ∪ D) 2 :=
  wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct hψ G H D E
    hC hM0 (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Constant product-form control with exact coefficient norms proves the raw fourth target after
deleting an additional left-hand spike set `E`. -/
theorem rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {C M : ℝ}
    (hC : C ≤ Real.sqrt 3) (hM0 : 0 ≤ M)
    (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    RawFourthMomentWithDiagonal ψ G H (E ∪ D) :=
  rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct hψ G H D E
    hC hM0 (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Constant product-form control plus a matching coefficient lower bound proves away-Wick at
`r = 2`. -/
theorem wickForIncidenceAwayAt_two_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {C M : ℝ}
    (hC : C ≤ Real.sqrt 3) (hM0 : 0 ≤ M)
    (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    WickForIncidenceAwayAt ψ G H D 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeConstSqrtCardMulSupProduct hψ G H D
    hC hM0 (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Constant product-form control plus a matching coefficient lower bound proves the raw fourth
target. -/
theorem rawFourthMomentWithDiagonal_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {C M : ℝ}
    (hC : C ≤ Real.sqrt 3) (hM0 : 0 ≤ M)
    (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    RawFourthMomentWithDiagonal ψ G H D :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeConstSqrtCardMulSupProduct hψ G H D
    hC hM0 (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Constant product-form control plus a matching coefficient lower bound proves away-Wick at
`r = 2` after deleting an additional spike set `E`. -/
theorem wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {C M : ℝ}
    (hC : C ≤ Real.sqrt 3) (hM0 : 0 ≤ M)
    (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    WickForIncidenceAwayAt ψ G H (D ∪ E) 2 :=
  wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct hψ G H D E
    hC hM0 (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Constant product-form control plus a matching coefficient lower bound proves the raw fourth
target after deleting an additional spike set `E`. -/
theorem rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {C M : ℝ}
    (hC : C ≤ Real.sqrt 3) (hM0 : 0 ≤ M)
    (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    RawFourthMomentWithDiagonal ψ G H (D ∪ E) :=
  rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct hψ G H D E
    hC hM0 (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Constant product-form control plus a matching coefficient lower bound proves away-Wick at
`r = 2` after deleting an additional left-hand spike set `E`. -/
theorem wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {C M : ℝ}
    (hC : C ≤ Real.sqrt 3) (hM0 : 0 ≤ M)
    (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    WickForIncidenceAwayAt ψ G H (E ∪ D) 2 :=
  wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct hψ G H D E
    hC hM0 (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Constant product-form control plus a matching coefficient lower bound proves the raw fourth
target after deleting an additional left-hand spike set `E`. -/
theorem rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {C M : ℝ}
    (hC : C ≤ Real.sqrt 3) (hM0 : 0 ≤ M)
    (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeConstSqrtCardMulSupProduct ψ G H D C M) :
    RawFourthMomentWithDiagonal ψ G H (E ∪ D) :=
  rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct hψ G H D E
    hC hM0 (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Familiar product-form control plus the energy-lower hypothesis proves away-Wick at `r = 2`. -/
theorem wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtCardMulSupProduct
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeSqrtCardMulSupProduct ψ G H D M) :
    WickForIncidenceAwayAt ψ G H D 2 := by
  have h1sqrt3 : (1 : ℝ) ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]
  exact wickForIncidenceAwayAt_two_of_offdiagNormLeConstSqrtCardMulSupProduct hψ G H D
    h1sqrt3 hM0 henergy
    (offdiagNormLeConstSqrtCardMulSupProduct_one_of_product G H D M hpt)

/-- Familiar product-form control plus the energy-lower hypothesis proves the raw fourth target. -/
theorem rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtCardMulSupProduct
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeSqrtCardMulSupProduct ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H D := by
  have h1sqrt3 : (1 : ℝ) ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]
  exact rawFourthMomentWithDiagonal_of_offdiagNormLeConstSqrtCardMulSupProduct hψ G H D
    h1sqrt3 hM0 henergy
    (offdiagNormLeConstSqrtCardMulSupProduct_one_of_product G H D M hpt)

/-- Familiar product-form control plus the energy-lower hypothesis proves away-Wick at `r = 2`
after deleting an additional spike set `E`. -/
theorem wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtCardMulSupProduct
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeSqrtCardMulSupProduct ψ G H D M) :
    WickForIncidenceAwayAt ψ G H (D ∪ E) 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtCardMulSupProduct hψ G H (D ∪ E)
    hM0 henergy (offdiagNormLeSqrtCardMulSupProduct_mono_deleted G H
      (by intro s hs; exact Finset.mem_union_left E hs) M hpt)

/-- Familiar product-form control plus the energy-lower hypothesis proves the raw fourth target
after deleting an additional spike set `E`. -/
theorem rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtCardMulSupProduct
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeSqrtCardMulSupProduct ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H (D ∪ E) :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtCardMulSupProduct hψ G H (D ∪ E)
    hM0 henergy (offdiagNormLeSqrtCardMulSupProduct_mono_deleted G H
      (by intro s hs; exact Finset.mem_union_left E hs) M hpt)

/-- Familiar product-form control plus the energy-lower hypothesis proves away-Wick at `r = 2`
after deleting an additional left-hand spike set `E`. -/
theorem wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSupProduct
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeSqrtCardMulSupProduct ψ G H D M) :
    WickForIncidenceAwayAt ψ G H (E ∪ D) 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtCardMulSupProduct hψ G H (E ∪ D)
    hM0 henergy (offdiagNormLeSqrtCardMulSupProduct_mono_deleted G H
      (by intro s hs; exact Finset.mem_union_right E hs) M hpt)

/-- Familiar product-form control plus the energy-lower hypothesis proves the raw fourth target
after deleting an additional left-hand spike set `E`. -/
theorem rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSupProduct
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeSqrtCardMulSupProduct ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H (E ∪ D) :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtCardMulSupProduct hψ G H (E ∪ D)
    hM0 henergy (offdiagNormLeSqrtCardMulSupProduct_mono_deleted G H
      (by intro s hs; exact Finset.mem_union_right E hs) M hpt)

/-- Familiar product-form control with exact coefficient norms proves away-Wick at `r = 2`. -/
theorem wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtCardMulSupProduct_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeSqrtCardMulSupProduct ψ G H D M) :
    WickForIncidenceAwayAt ψ G H D 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtCardMulSupProduct hψ G H D hM0
    (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Familiar product-form control with exact coefficient norms proves the raw fourth target. -/
theorem rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtCardMulSupProduct_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeSqrtCardMulSupProduct ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H D :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtCardMulSupProduct hψ G H D hM0
    (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Familiar product-form control with exact coefficient norms proves away-Wick at `r = 2` after
deleting an additional spike set `E`. -/
theorem wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtCardMulSupProduct_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeSqrtCardMulSupProduct ψ G H D M) :
    WickForIncidenceAwayAt ψ G H (D ∪ E) 2 :=
  wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtCardMulSupProduct hψ G H D E
    hM0 (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Familiar product-form control with exact coefficient norms proves the raw fourth target after
deleting an additional spike set `E`. -/
theorem rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtCardMulSupProduct_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeSqrtCardMulSupProduct ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H (D ∪ E) :=
  rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtCardMulSupProduct hψ G H D E
    hM0 (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Familiar product-form control with exact coefficient norms proves away-Wick at `r = 2` after
deleting an additional left-hand spike set `E`. -/
theorem wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSupProduct_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeSqrtCardMulSupProduct ψ G H D M) :
    WickForIncidenceAwayAt ψ G H (E ∪ D) 2 :=
  wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSupProduct hψ G H D E
    hM0 (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Familiar product-form control with exact coefficient norms proves the raw fourth target after
deleting an additional left-hand spike set `E`. -/
theorem rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSupProduct_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeSqrtCardMulSupProduct ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H (E ∪ D) :=
  rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSupProduct hψ G H D E
    hM0 (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Familiar product-form control plus a matching coefficient lower bound proves away-Wick at
`r = 2`.  The lower bound discharges the energy-lower hypothesis. -/
theorem wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtCardMulSupProduct_of_coeff_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeSqrtCardMulSupProduct ψ G H D M) :
    WickForIncidenceAwayAt ψ G H D 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtCardMulSupProduct hψ G H D hM0
    (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Familiar product-form control plus a matching coefficient lower bound proves the raw fourth
target. -/
theorem rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtCardMulSupProduct_of_coeff_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeSqrtCardMulSupProduct ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H D :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtCardMulSupProduct hψ G H D hM0
    (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Familiar product-form control plus a matching coefficient lower bound proves away-Wick at
`r = 2` after deleting an additional spike set `E`. -/
theorem wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtCardMulSupProduct_of_coeff_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeSqrtCardMulSupProduct ψ G H D M) :
    WickForIncidenceAwayAt ψ G H (D ∪ E) 2 :=
  wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtCardMulSupProduct hψ G H D E
    hM0 (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Familiar product-form control plus a matching coefficient lower bound proves the raw fourth
target after deleting an additional spike set `E`. -/
theorem rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtCardMulSupProduct_of_coeff_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeSqrtCardMulSupProduct ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H (D ∪ E) :=
  rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtCardMulSupProduct hψ G H D E
    hM0 (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Familiar product-form control plus a matching coefficient lower bound proves away-Wick at
`r = 2` after deleting an additional left-hand spike set `E`. -/
theorem wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSupProduct_of_coeff_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeSqrtCardMulSupProduct ψ G H D M) :
    WickForIncidenceAwayAt ψ G H (E ∪ D) 2 :=
  wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSupProduct hψ G H D E
    hM0 (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Familiar product-form control plus a matching coefficient lower bound proves the raw fourth
target after deleting an additional left-hand spike set `E`. -/
theorem rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSupProduct_of_coeff_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeSqrtCardMulSupProduct ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H (E ∪ D) :=
  rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSupProduct hψ G H D E
    hM0 (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Square-root-card control plus the energy-lower hypothesis proves away-Wick at `r = 2`. -/
theorem wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtCardMulSup
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeSqrtCardMulSup ψ G H D M) :
    WickForIncidenceAwayAt ψ G H D 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtCardMulSupProduct hψ G H D
    hM0 henergy (offdiagNormLeSqrtCardMulSupProduct_of_sqrtCardMulSup G H D hM0 hpt)

/-- Square-root-card control plus the energy-lower hypothesis proves the raw fourth target. -/
theorem rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtCardMulSup
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeSqrtCardMulSup ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H D :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtCardMulSupProduct hψ G H D
    hM0 henergy (offdiagNormLeSqrtCardMulSupProduct_of_sqrtCardMulSup G H D hM0 hpt)

/-- Square-root-card control plus the energy-lower hypothesis proves away-Wick at `r = 2` after
deleting an additional spike set `E`. -/
theorem wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtCardMulSup
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeSqrtCardMulSup ψ G H D M) :
    WickForIncidenceAwayAt ψ G H (D ∪ E) 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtCardMulSup hψ G H (D ∪ E)
    hM0 henergy (offdiagNormLeSqrtCardMulSup_mono_deleted G H
      (by intro s hs; exact Finset.mem_union_left E hs) M hpt)

/-- Square-root-card control plus the energy-lower hypothesis proves the raw fourth target after
deleting an additional spike set `E`. -/
theorem rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtCardMulSup
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeSqrtCardMulSup ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H (D ∪ E) :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtCardMulSup hψ G H (D ∪ E)
    hM0 henergy (offdiagNormLeSqrtCardMulSup_mono_deleted G H
      (by intro s hs; exact Finset.mem_union_left E hs) M hpt)

/-- Square-root-card control plus the energy-lower hypothesis proves away-Wick at `r = 2` after
deleting an additional left-hand spike set `E`. -/
theorem wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSup
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeSqrtCardMulSup ψ G H D M) :
    WickForIncidenceAwayAt ψ G H (E ∪ D) 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtCardMulSup hψ G H (E ∪ D)
    hM0 henergy (offdiagNormLeSqrtCardMulSup_mono_deleted G H
      (by intro s hs; exact Finset.mem_union_right E hs) M hpt)

/-- Square-root-card control plus the energy-lower hypothesis proves the raw fourth target after
deleting an additional left-hand spike set `E`. -/
theorem rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSup
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeSqrtCardMulSup ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H (E ∪ D) :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtCardMulSup hψ G H (E ∪ D)
    hM0 henergy (offdiagNormLeSqrtCardMulSup_mono_deleted G H
      (by intro s hs; exact Finset.mem_union_right E hs) M hpt)

/-- Square-root-card control with exact coefficient norms proves away-Wick at `r = 2`. -/
theorem wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtCardMulSup_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeSqrtCardMulSup ψ G H D M) :
    WickForIncidenceAwayAt ψ G H D 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtCardMulSup hψ G H D hM0
    (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Square-root-card control with exact coefficient norms proves the raw fourth target. -/
theorem rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtCardMulSup_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeSqrtCardMulSup ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H D :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtCardMulSup hψ G H D hM0
    (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Square-root-card control with exact coefficient norms proves away-Wick at `r = 2` after
deleting an additional spike set `E`. -/
theorem wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtCardMulSup_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeSqrtCardMulSup ψ G H D M) :
    WickForIncidenceAwayAt ψ G H (D ∪ E) 2 :=
  wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtCardMulSup hψ G H D E
    hM0 (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Square-root-card control with exact coefficient norms proves the raw fourth target after
deleting an additional spike set `E`. -/
theorem rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtCardMulSup_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeSqrtCardMulSup ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H (D ∪ E) :=
  rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtCardMulSup hψ G H D E
    hM0 (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Square-root-card control with exact coefficient norms proves away-Wick at `r = 2` after
deleting an additional left-hand spike set `E`. -/
theorem wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSup_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeSqrtCardMulSup ψ G H D M) :
    WickForIncidenceAwayAt ψ G H (E ∪ D) 2 :=
  wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSup hψ G H D E
    hM0 (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Square-root-card control with exact coefficient norms proves the raw fourth target after
deleting an additional left-hand spike set `E`. -/
theorem rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSup_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeSqrtCardMulSup ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H (E ∪ D) :=
  rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSup hψ G H D E
    hM0 (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Square-root-card control plus a matching coefficient lower bound proves away-Wick at `r = 2`.
The lower bound discharges the energy-lower hypothesis. -/
theorem wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtCardMulSup_of_coeff_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeSqrtCardMulSup ψ G H D M) :
    WickForIncidenceAwayAt ψ G H D 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtCardMulSup hψ G H D hM0
    (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Square-root-card control plus a matching coefficient lower bound proves the raw fourth target.
-/
theorem rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtCardMulSup_of_coeff_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeSqrtCardMulSup ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H D :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtCardMulSup hψ G H D hM0
    (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Square-root-card control plus a matching coefficient lower bound proves away-Wick at `r = 2`
after deleting an additional spike set `E`. -/
theorem wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtCardMulSup_of_coeff_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeSqrtCardMulSup ψ G H D M) :
    WickForIncidenceAwayAt ψ G H (D ∪ E) 2 :=
  wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtCardMulSup hψ G H D E
    hM0 (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Square-root-card control plus a matching coefficient lower bound proves the raw fourth target
after deleting an additional spike set `E`. -/
theorem rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtCardMulSup_of_coeff_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeSqrtCardMulSup ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H (D ∪ E) :=
  rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtCardMulSup hψ G H D E
    hM0 (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Square-root-card control plus a matching coefficient lower bound proves away-Wick at `r = 2`
after deleting an additional left-hand spike set `E`. -/
theorem wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSup_of_coeff_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeSqrtCardMulSup ψ G H D M) :
    WickForIncidenceAwayAt ψ G H (E ∪ D) 2 :=
  wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSup hψ G H D E
    hM0 (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Square-root-card control plus a matching coefficient lower bound proves the raw fourth target
after deleting an additional left-hand spike set `E`. -/
theorem rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSup_of_coeff_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeSqrtCardMulSup ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H (E ∪ D) :=
  rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSup hψ G H D E
    hM0 (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Product-form `sqrt(3)` control implies variance-scale `sqrt(3)` control when the sup envelope
does not exceed the actual coefficient energy: `|H|·M² ≤ Σ`.  This is the honest extra hypothesis
needed to feed a product-form estimate into the first-rung Wick route. -/
theorem offdiagNormLeSqrtThreeSigma_of_offdiagNormLeSqrtThreeCardMulSupProduct
    {ψ : AddChar F ℂ} (G H D : Finset F) {M : ℝ} (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M) :
    OffdiagNormLeSqrtThreeSigma ψ G H D := by
  intro s₀ hs₀
  refine le_trans (hpt s₀ hs₀) ?_
  have hcard_nonneg : 0 ≤ (H.card : ℝ) := by positivity
  have hscale :
      Real.sqrt (H.card : ℝ) * M
        ≤ Real.sqrt (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) := by
    calc Real.sqrt (H.card : ℝ) * M
        = Real.sqrt ((H.card : ℝ) * M ^ 2) := by
            rw [Real.sqrt_mul hcard_nonneg, Real.sqrt_sq hM0]
      _ ≤ Real.sqrt (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) := Real.sqrt_le_sqrt henergy
  exact mul_le_mul_of_nonneg_left hscale (Real.sqrt_nonneg 3)

/-- Product-form `sqrt(3)` control plus the energy-lower hypothesis proves away-Wick at `r = 2`. -/
theorem wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtThreeCardMulSupProduct
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M) :
    WickForIncidenceAwayAt ψ G H D 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtThreeSigma hψ G H D
    (offdiagNormLeSqrtThreeSigma_of_offdiagNormLeSqrtThreeCardMulSupProduct G H D hM0
      henergy hpt)

/-- Product-form `sqrt(3)` control plus the energy-lower hypothesis proves the raw fourth target. -/
theorem rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtThreeCardMulSupProduct
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H D :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtThreeSigma hψ G H D
    (offdiagNormLeSqrtThreeSigma_of_offdiagNormLeSqrtThreeCardMulSupProduct G H D hM0
      henergy hpt)

/-- Product-form `sqrt(3)` control plus the energy-lower hypothesis proves away-Wick at `r = 2`
after deleting an additional spike set `E`. -/
theorem wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M) :
    WickForIncidenceAwayAt ψ G H (D ∪ E) 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtThreeCardMulSupProduct hψ G H (D ∪ E)
    hM0 henergy (offdiagNormLeSqrtThreeCardMulSupProduct_union_deleted G H D E M hpt)

/-- Product-form `sqrt(3)` control plus the energy-lower hypothesis proves the raw fourth target
after deleting an additional spike set `E`. -/
theorem rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H (D ∪ E) :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtThreeCardMulSupProduct hψ G H (D ∪ E)
    hM0 henergy (offdiagNormLeSqrtThreeCardMulSupProduct_union_deleted G H D E M hpt)

/-- Product-form `sqrt(3)` control plus the energy-lower hypothesis proves away-Wick at `r = 2`
after deleting an additional left-hand spike set `E`. -/
theorem wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M) :
    WickForIncidenceAwayAt ψ G H (E ∪ D) 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtThreeCardMulSupProduct hψ G H (E ∪ D)
    hM0 henergy (offdiagNormLeSqrtThreeCardMulSupProduct_leftUnion_deleted G H D E M hpt)

/-- Product-form `sqrt(3)` control plus the energy-lower hypothesis proves the raw fourth target
after deleting an additional left-hand spike set `E`. -/
theorem rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M)
    (henergy : (H.card : ℝ) * M ^ 2 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hpt : OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H (E ∪ D) :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtThreeCardMulSupProduct hψ G H (E ∪ D)
    hM0 henergy (offdiagNormLeSqrtThreeCardMulSupProduct_leftUnion_deleted G H D E M hpt)

/-- Product-form `sqrt(3)` control with a matching coefficient lower bound implies the exact
`sqrt(3)` variance-scale target. -/
theorem offdiagNormLeSqrtThreeSigma_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_lower
    {ψ : AddChar F ℂ} (G H D : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M) :
    OffdiagNormLeSqrtThreeSigma ψ G H D :=
  offdiagNormLeSqrtThreeSigma_of_offdiagNormLeSqrtThreeCardMulSupProduct G H D hM0
    (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Product-form `sqrt(3)` control with exact coefficient norms implies the exact `sqrt(3)`
variance-scale target. -/
theorem offdiagNormLeSqrtThreeSigma_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (G H D : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M) :
    OffdiagNormLeSqrtThreeSigma ψ G H D :=
  offdiagNormLeSqrtThreeSigma_of_offdiagNormLeSqrtThreeCardMulSupProduct G H D hM0
    (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Product-form `sqrt(3)` control with exact coefficient norms proves away-Wick at `r = 2`. -/
theorem wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M) :
    WickForIncidenceAwayAt ψ G H D 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtThreeCardMulSupProduct hψ G H D hM0
    (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Product-form `sqrt(3)` control with exact coefficient norms proves the raw fourth target. -/
theorem rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H D :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtThreeCardMulSupProduct hψ G H D hM0
    (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Product-form `sqrt(3)` control with exact coefficient norms proves away-Wick at `r = 2` after
deleting an additional spike set `E`. -/
theorem wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M) :
    WickForIncidenceAwayAt ψ G H (D ∪ E) 2 :=
  wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct hψ G H D E
    hM0 (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Product-form `sqrt(3)` control with exact coefficient norms proves the raw fourth target after
deleting an additional spike set `E`. -/
theorem rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H (D ∪ E) :=
  rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct hψ G H D E
    hM0 (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Product-form `sqrt(3)` control with exact coefficient norms proves away-Wick at `r = 2` after
deleting an additional left-hand spike set `E`. -/
theorem wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M) :
    WickForIncidenceAwayAt ψ G H (E ∪ D) 2 :=
  wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct hψ G H D E
    hM0 (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Product-form `sqrt(3)` control with exact coefficient norms proves the raw fourth target after
deleting an additional left-hand spike set `E`. -/
theorem rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_norm_eq
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMeq : ∀ b ∈ H, ‖eta ψ G b‖ = M)
    (hpt : OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H (E ∪ D) :=
  rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct hψ G H D E
    hM0 (card_mul_sq_le_energy_of_coeff_norm_eq G H hMeq) hpt

/-- Product-form `sqrt(3)` control with a matching coefficient lower bound proves away-Wick at
`r = 2`. -/
theorem wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M) :
    WickForIncidenceAwayAt ψ G H D 2 :=
  wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtThreeCardMulSupProduct hψ G H D hM0
    (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Product-form `sqrt(3)` control with a matching coefficient lower bound proves the raw fourth
target. -/
theorem rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H D :=
  rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtThreeCardMulSupProduct hψ G H D hM0
    (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Product-form `sqrt(3)` control with a matching coefficient lower bound proves away-Wick at
`r = 2` after deleting an additional spike set `E`. -/
theorem wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M) :
    WickForIncidenceAwayAt ψ G H (D ∪ E) 2 :=
  wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct hψ G H D E
    hM0 (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Product-form `sqrt(3)` control with a matching coefficient lower bound proves the raw fourth
target after deleting an additional spike set `E`. -/
theorem rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H (D ∪ E) :=
  rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct hψ G H D E
    hM0 (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Product-form `sqrt(3)` control with a matching coefficient lower bound proves away-Wick at
`r = 2` after deleting an additional left-hand spike set `E`. -/
theorem wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M) :
    WickForIncidenceAwayAt ψ G H (E ∪ D) 2 :=
  wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct hψ G H D E
    hM0 (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- Product-form `sqrt(3)` control with a matching coefficient lower bound proves the raw fourth
target after deleting an additional left-hand spike set `E`. -/
theorem rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D E : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hMlower : ∀ b ∈ H, M ≤ ‖eta ψ G b‖)
    (hpt : OffdiagNormLeSqrtThreeCardMulSupProduct ψ G H D M) :
    RawFourthMomentWithDiagonal ψ G H (E ∪ D) :=
  rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct hψ G H D E
    hM0 (card_mul_sq_le_energy_of_coeff_lower_bound G H hM0 hMlower) hpt

/-- **Exact diagonal-cancellation equivalence.**  The corrected rung `WickForIncidenceAwayAt` is
equivalent to the raw moment bound with the exact excluded diagonal mass added back to the Wick
right-hand side.  This is the cleanest interface for expanded-moment attacks: prove either side,
and Lean can switch to the other by the identity
`S_r = S_r^D + diagonalMass(D)`. -/
theorem wickForIncidenceAwayAt_iff_incidenceMoment_le_wick_add_diag {ψ : AddChar F ℂ}
    (G H D : Finset F) (r : ℕ) :
    WickForIncidenceAwayAt ψ G H D r
      ↔ incidenceMoment ψ G H r
          ≤ (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
              * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r
            + ∑ s₀ ∈ D, ‖incidenceSum ψ G H s₀‖ ^ (2 * r) := by
  constructor
  · intro haway
    unfold WickForIncidenceAwayAt at haway
    rw [incidenceMoment_eq_away_add_diag ψ G H D r]
    linarith
  · exact wickForIncidenceAwayAt_of_incidenceMoment_le_wick_add_diag G H D r

/-- Named-Prop exact diagonal-cancellation equivalence. -/
theorem wickForIncidenceAwayAt_iff_rawIncidenceMomentWithDiagonalAt
    {ψ : AddChar F ℂ} (G H D : Finset F) (r : ℕ) :
    WickForIncidenceAwayAt ψ G H D r
      ↔ RawIncidenceMomentWithDiagonalAt ψ G H D r := by
  simpa [RawIncidenceMomentWithDiagonalAt] using
    (wickForIncidenceAwayAt_iff_incidenceMoment_le_wick_add_diag G H D r)

/-- Full-tower named-Prop exact diagonal-cancellation equivalence. -/
theorem wickForIncidenceAway_iff_rawIncidenceMomentWithDiagonal
    {ψ : AddChar F ℂ} (G H D : Finset F) :
    WickForIncidenceAway ψ G H D
      ↔ RawIncidenceMomentWithDiagonal ψ G H D := by
  constructor
  · intro haway r
    exact (wickForIncidenceAwayAt_iff_rawIncidenceMomentWithDiagonalAt G H D r).mp (haway r)
  · intro hraw r
    exact (wickForIncidenceAwayAt_iff_rawIncidenceMomentWithDiagonalAt G H D r).mpr (hraw r)

/-- Full-tower form of diagonal-mass cancellation.  If every raw rung is bounded by Wick plus the
exact excluded diagonal mass, then the corrected diagonal-subtracted Wick tower holds. -/
theorem wickForIncidenceAway_of_incidenceMoment_le_wick_add_diag {ψ : AddChar F ℂ}
    (G H D : Finset F)
    (hraw : ∀ r : ℕ,
      incidenceMoment ψ G H r
        ≤ (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
            * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r
          + ∑ s₀ ∈ D, ‖incidenceSum ψ G H s₀‖ ^ (2 * r)) :
    WickForIncidenceAway ψ G H D := by
  intro r
  exact wickForIncidenceAwayAt_of_incidenceMoment_le_wick_add_diag G H D r (hraw r)

/-- Higher-rung form of diagonal-mass cancellation.  Since rungs `0` and `1` are already proved,
it is enough to supply the raw-plus-diagonal estimate for `r ≥ 2`. -/
theorem wickForIncidenceAway_of_high_incidenceMoment_le_wick_add_diag {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G H D : Finset F)
    (hraw : ∀ r : ℕ, 2 ≤ r →
      incidenceMoment ψ G H r
        ≤ (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
            * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r
          + ∑ s₀ ∈ D, ‖incidenceSum ψ G H s₀‖ ^ (2 * r)) :
    WickForIncidenceAway ψ G H D := by
  refine wickForIncidenceAway_of_ge_two hψ G H D ?_
  intro r hr
  exact wickForIncidenceAwayAt_of_incidenceMoment_le_wick_add_diag G H D r (hraw r hr)

/-- **Uniform envelope for the excluded diagonal mass.**  If every excluded offset has
`‖I_H(s₀)‖ ≤ B`, then its contribution to the `2r`-moment is at most `|D| · B^(2r)`.
This is the coarse companion to `wickForIncidenceAwayAt_of_incidenceMoment_le_wick_add_diag`: exact
diagonal cancellation is preferred, but a spike/tail envelope can be inserted when an analytic
estimate needs a numerical budget for the deleted offsets. -/
theorem diagonalMass_le_card_mul_bound {ψ : AddChar F ℂ} (G H D : Finset F)
    (r : ℕ) {B : ℝ} (_hB0 : 0 ≤ B)
    (hB : ∀ s₀ ∈ D, ‖incidenceSum ψ G H s₀‖ ≤ B) :
    (∑ s₀ ∈ D, ‖incidenceSum ψ G H s₀‖ ^ (2 * r))
      ≤ (D.card : ℝ) * B ^ (2 * r) := by
  classical
  calc (∑ s₀ ∈ D, ‖incidenceSum ψ G H s₀‖ ^ (2 * r))
      ≤ ∑ _s₀ ∈ D, B ^ (2 * r) := by
        refine Finset.sum_le_sum (fun s₀ hs₀ => ?_)
        exact pow_le_pow_left₀ (norm_nonneg _) (hB s₀ hs₀) (2 * r)
    _ = (D.card : ℝ) * B ^ (2 * r) := by
        rw [Finset.sum_const, nsmul_eq_mul]

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

/-- Raw full-tower Wick implies the corrected full tower.  This is logically weaker than the
prize-relevant corrected target because raw Wick is probe-refuted, but it records the exact
relationship between the old and corrected hypotheses. -/
theorem wickForIncidenceAway_of_wickForIncidence {ψ : AddChar F ℂ} (G H D : Finset F)
    (hwick : WickForIncidence ψ G H) :
    WickForIncidenceAway ψ G H D := by
  intro r
  exact wickForIncidenceAwayAt_of_wickForIncidence G H D hwick r

/-- **Monotonicity of the corrected Wick target.**  If the diagonal-subtracted Wick rung holds
after deleting `D`, then it also holds after deleting any larger diagonal set `D'`. -/
theorem wickForIncidenceAwayAt_mono_deleted {ψ : AddChar F ℂ} (G H : Finset F)
    {D D' : Finset F} (hDD' : D ⊆ D') (r : ℕ)
    (hwick : WickForIncidenceAwayAt ψ G H D r) :
    WickForIncidenceAwayAt ψ G H D' r := by
  exact le_trans (incidenceMomentAway_antitone_deleted ψ G H hDD' r) hwick

/-- Full-tower monotonicity in the deleted diagonal set. -/
theorem wickForIncidenceAway_mono_deleted {ψ : AddChar F ℂ} (G H : Finset F)
    {D D' : Finset F} (hDD' : D ⊆ D')
    (hwick : WickForIncidenceAway ψ G H D) :
    WickForIncidenceAway ψ G H D' := by
  intro r
  exact wickForIncidenceAwayAt_mono_deleted G H hDD' r (hwick r)

/-- Monotonicity of the raw-with-diagonal target in the deleted set.  Enlarging `D` only enlarges
the diagonal allowance on the right-hand side. -/
theorem rawIncidenceMomentWithDiagonalAt_mono_deleted {ψ : AddChar F ℂ} (G H : Finset F)
    {D D' : Finset F} (hDD' : D ⊆ D') (r : ℕ)
    (hraw : RawIncidenceMomentWithDiagonalAt ψ G H D r) :
    RawIncidenceMomentWithDiagonalAt ψ G H D' r := by
  classical
  unfold RawIncidenceMomentWithDiagonalAt at hraw ⊢
  have hdiag :
      (∑ s₀ ∈ D, ‖incidenceSum ψ G H s₀‖ ^ (2 * r))
        ≤ ∑ s₀ ∈ D', ‖incidenceSum ψ G H s₀‖ ^ (2 * r) :=
    Finset.sum_le_sum_of_subset_of_nonneg hDD'
      (by intro s _ _; positivity)
  linarith

/-- Full-tower monotonicity of the raw-with-diagonal target in the deleted set. -/
theorem rawIncidenceMomentWithDiagonal_mono_deleted {ψ : AddChar F ℂ} (G H : Finset F)
    {D D' : Finset F} (hDD' : D ⊆ D')
    (hraw : RawIncidenceMomentWithDiagonal ψ G H D) :
    RawIncidenceMomentWithDiagonal ψ G H D' := by
  intro r
  exact rawIncidenceMomentWithDiagonalAt_mono_deleted G H hDD' r (hraw r)

/-- Monotonicity of the named raw fourth-moment target in the deleted set. -/
theorem rawFourthMomentWithDiagonal_mono_deleted {ψ : AddChar F ℂ} (G H : Finset F)
    {D D' : Finset F} (hDD' : D ⊆ D')
    (hraw : RawFourthMomentWithDiagonal ψ G H D) :
    RawFourthMomentWithDiagonal ψ G H D' := by
  classical
  unfold RawFourthMomentWithDiagonal at hraw ⊢
  have hdiag :
      (∑ s₀ ∈ D, ‖incidenceSum ψ G H s₀‖ ^ 4)
        ≤ ∑ s₀ ∈ D', ‖incidenceSum ψ G H s₀‖ ^ 4 :=
    Finset.sum_le_sum_of_subset_of_nonneg hDD'
      (by intro s _ _; positivity)
  linarith

/-- Enlarge a corrected Wick rung by deleting an additional spike set `E`. -/
theorem wickForIncidenceAwayAt_union_deleted {ψ : AddChar F ℂ} (G H D E : Finset F)
    (r : ℕ) (hwick : WickForIncidenceAwayAt ψ G H D r) :
    WickForIncidenceAwayAt ψ G H (D ∪ E) r :=
  wickForIncidenceAwayAt_mono_deleted G H
    (by intro s hs; exact Finset.mem_union_left E hs) r hwick

/-- Enlarge the corrected Wick tower by deleting an additional spike set `E`. -/
theorem wickForIncidenceAway_union_deleted {ψ : AddChar F ℂ} (G H D E : Finset F)
    (hwick : WickForIncidenceAway ψ G H D) :
    WickForIncidenceAway ψ G H (D ∪ E) :=
  wickForIncidenceAway_mono_deleted G H
    (by intro s hs; exact Finset.mem_union_left E hs) hwick

/-- Enlarge the raw-with-diagonal rung by deleting an additional spike set `E`. -/
theorem rawIncidenceMomentWithDiagonalAt_union_deleted {ψ : AddChar F ℂ}
    (G H D E : Finset F) (r : ℕ)
    (hraw : RawIncidenceMomentWithDiagonalAt ψ G H D r) :
    RawIncidenceMomentWithDiagonalAt ψ G H (D ∪ E) r :=
  rawIncidenceMomentWithDiagonalAt_mono_deleted G H
    (by intro s hs; exact Finset.mem_union_left E hs) r hraw

/-- Enlarge the raw-with-diagonal tower by deleting an additional spike set `E`. -/
theorem rawIncidenceMomentWithDiagonal_union_deleted {ψ : AddChar F ℂ}
    (G H D E : Finset F)
    (hraw : RawIncidenceMomentWithDiagonal ψ G H D) :
    RawIncidenceMomentWithDiagonal ψ G H (D ∪ E) :=
  rawIncidenceMomentWithDiagonal_mono_deleted G H
    (by intro s hs; exact Finset.mem_union_left E hs) hraw

/-- Enlarge the named raw fourth-moment target by deleting an additional spike set `E`. -/
theorem rawFourthMomentWithDiagonal_union_deleted {ψ : AddChar F ℂ} (G H D E : Finset F)
    (hraw : RawFourthMomentWithDiagonal ψ G H D) :
    RawFourthMomentWithDiagonal ψ G H (D ∪ E) :=
  rawFourthMomentWithDiagonal_mono_deleted G H
    (by intro s hs; exact Finset.mem_union_left E hs) hraw

/-- Enlarge a corrected Wick rung by deleting an additional left-hand spike set `E`. -/
theorem wickForIncidenceAwayAt_leftUnion_deleted {ψ : AddChar F ℂ} (G H D E : Finset F)
    (r : ℕ) (hwick : WickForIncidenceAwayAt ψ G H D r) :
    WickForIncidenceAwayAt ψ G H (E ∪ D) r :=
  wickForIncidenceAwayAt_mono_deleted G H
    (by intro s hs; exact Finset.mem_union_right E hs) r hwick

/-- Enlarge the corrected Wick tower by deleting an additional left-hand spike set `E`. -/
theorem wickForIncidenceAway_leftUnion_deleted {ψ : AddChar F ℂ} (G H D E : Finset F)
    (hwick : WickForIncidenceAway ψ G H D) :
    WickForIncidenceAway ψ G H (E ∪ D) :=
  wickForIncidenceAway_mono_deleted G H
    (by intro s hs; exact Finset.mem_union_right E hs) hwick

/-- Enlarge the raw-with-diagonal rung by deleting an additional left-hand spike set `E`. -/
theorem rawIncidenceMomentWithDiagonalAt_leftUnion_deleted {ψ : AddChar F ℂ}
    (G H D E : Finset F) (r : ℕ)
    (hraw : RawIncidenceMomentWithDiagonalAt ψ G H D r) :
    RawIncidenceMomentWithDiagonalAt ψ G H (E ∪ D) r :=
  rawIncidenceMomentWithDiagonalAt_mono_deleted G H
    (by intro s hs; exact Finset.mem_union_right E hs) r hraw

/-- Enlarge the raw-with-diagonal tower by deleting an additional left-hand spike set `E`. -/
theorem rawIncidenceMomentWithDiagonal_leftUnion_deleted {ψ : AddChar F ℂ}
    (G H D E : Finset F)
    (hraw : RawIncidenceMomentWithDiagonal ψ G H D) :
    RawIncidenceMomentWithDiagonal ψ G H (E ∪ D) :=
  rawIncidenceMomentWithDiagonal_mono_deleted G H
    (by intro s hs; exact Finset.mem_union_right E hs) hraw

/-- Enlarge the named raw fourth-moment target by deleting an additional left-hand spike set `E`. -/
theorem rawFourthMomentWithDiagonal_leftUnion_deleted {ψ : AddChar F ℂ}
    (G H D E : Finset F) (hraw : RawFourthMomentWithDiagonal ψ G H D) :
    RawFourthMomentWithDiagonal ψ G H (E ∪ D) :=
  rawFourthMomentWithDiagonal_mono_deleted G H
    (by intro s hs; exact Finset.mem_union_right E hs) hraw

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
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.incidenceMomentAway_antitone_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_zero
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_one
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAway_of_ge_two
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_of_incidenceMoment_le_wick_add_diag
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_of_rawIncidenceMomentWithDiagonalAt
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_of_incidenceMoment_le_three_wick_add_diag
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_iff_incidenceMoment_le_three_wick_add_diag
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_iff_rawFourthMomentWithDiagonal
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_of_rawFourthMomentWithDiagonal
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_of_offdiag_sq_le_three_sigma
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_of_offdiag_sq_le_three_sigma
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_of_offdiagSquareLeThreeSigma
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_of_offdiagSquareLeThreeSigma
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_union_deleted_of_offdiagSquareLeThreeSigma
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_union_deleted_of_offdiagSquareLeThreeSigma
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagSquareLeThreeSigma
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagSquareLeThreeSigma
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagSquareLeThreeSigma_of_offdiagNormLeSqrtSigma
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtSigma
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtSigma
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtSigma_mono_const
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtThreeSigma_of_offdiagNormLeSqrtSigma_le
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtThreeSigma_of_offdiagNormLeSqrtSigmaOne
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagSquareLeThreeSigma_mono_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtSigma_mono_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtThreeSigma_mono_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtSigmaOne_mono_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtCardMulSup_mono_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtCardMulSupProduct_mono_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeConstSqrtCardMulSupProduct_mono_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtThreeCardMulSupProduct_mono_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagSquareLeThreeSigma_union_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtSigma_union_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtThreeSigma_union_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtSigmaOne_union_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtCardMulSup_union_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtCardMulSupProduct_union_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeConstSqrtCardMulSupProduct_union_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtThreeCardMulSupProduct_union_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagSquareLeThreeSigma_leftUnion_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtSigma_leftUnion_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtThreeSigma_leftUnion_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtSigmaOne_leftUnion_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtCardMulSup_leftUnion_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtCardMulSupProduct_leftUnion_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeConstSqrtCardMulSupProduct_leftUnion_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtThreeCardMulSupProduct_leftUnion_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagSquareLeThreeSigma_of_offdiagNormLeSqrtThreeSigma
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtThreeSigma
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtThreeSigma
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtThreeSigma
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtThreeSigma
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtThreeSigma
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtThreeSigma
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtSigma_le_sqrtThree
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtSigma_le_sqrtThree
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtSigma_le_sqrtThree
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtSigma_le_sqrtThree
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtSigma_le_sqrtThree
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtSigma_le_sqrtThree
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtSigmaOne
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtSigmaOne
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtSigmaOne
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtSigmaOne
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtSigmaOne
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtSigmaOne
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtCardMulSup_of_offdiagNormLeSqrtSigmaOne
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.card_mul_sq_le_energy_of_coeff_lower_bound
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.energy_eq_card_mul_sq_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.card_mul_sq_le_energy_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtCardMulSupProduct_of_sqrtCardMulSup
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtCardMulSupProduct_of_offdiagNormLeSqrtSigmaOne
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeConstSqrtCardMulSupProduct_of_offdiagNormLeSqrtSigma
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeConstSqrtCardMulSupProduct_one_of_product
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeConstSqrtCardMulSupProduct_mono_const
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtThreeCardMulSupProduct_of_offdiagNormLeSqrtCardMulSupProduct
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeConstSqrtCardMulSupProduct_of_product
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeConstSqrtCardMulSupProduct_of_sqrtCardMulSup
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtThreeCardMulSupProduct_of_offdiagNormLeSqrtSigmaOne
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtThreeCardMulSupProduct_of_offdiagNormLeSqrtThreeSigma
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtSigma_of_offdiagNormLeConstSqrtCardMulSupProduct
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtThreeSigma_of_offdiagNormLeConstSqrtCardMulSupProduct
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_of_offdiagNormLeConstSqrtCardMulSupProduct
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_of_offdiagNormLeConstSqrtCardMulSupProduct
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtSigma_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtThreeSigma_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtSigma_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtThreeSigma_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeConstSqrtCardMulSupProduct_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtCardMulSupProduct
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtCardMulSupProduct
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtCardMulSupProduct
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtCardMulSupProduct
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSupProduct
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSupProduct
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtCardMulSupProduct_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtCardMulSupProduct_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtCardMulSupProduct_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtCardMulSupProduct_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSupProduct_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSupProduct_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtCardMulSupProduct_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtCardMulSupProduct_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtCardMulSupProduct_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtCardMulSupProduct_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSupProduct_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSupProduct_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtCardMulSup
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtCardMulSup
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtCardMulSup
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtCardMulSup
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSup
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSup
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtCardMulSup_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtCardMulSup_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtCardMulSup_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtCardMulSup_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSup_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSup_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtCardMulSup_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtCardMulSup_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtCardMulSup_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtCardMulSup_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSup_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtCardMulSup_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtThreeSigma_of_offdiagNormLeSqrtThreeCardMulSupProduct
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtThreeCardMulSupProduct
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtThreeCardMulSupProduct
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtThreeSigma_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_norm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.offdiagNormLeSqrtThreeSigma_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_union_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_union_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_two_leftUnion_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_leftUnion_deleted_of_offdiagNormLeSqrtThreeCardMulSupProduct_of_coeff_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_iff_incidenceMoment_le_wick_add_diag
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_iff_rawIncidenceMomentWithDiagonalAt
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAway_iff_rawIncidenceMomentWithDiagonal
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAway_of_incidenceMoment_le_wick_add_diag
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAway_of_high_incidenceMoment_le_wick_add_diag
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_of_wickForIncidenceAt
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_of_wickForIncidence
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAway_of_wickForIncidence
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_mono_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAway_mono_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawIncidenceMomentWithDiagonalAt_mono_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawIncidenceMomentWithDiagonal_mono_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_mono_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_union_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAway_union_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawIncidenceMomentWithDiagonalAt_union_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawIncidenceMomentWithDiagonal_union_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_union_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAwayAt_leftUnion_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.wickForIncidenceAway_leftUnion_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawIncidenceMomentWithDiagonalAt_leftUnion_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawIncidenceMomentWithDiagonal_leftUnion_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.rawFourthMomentWithDiagonal_leftUnion_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.diagonalMass_le_card_mul_bound
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
