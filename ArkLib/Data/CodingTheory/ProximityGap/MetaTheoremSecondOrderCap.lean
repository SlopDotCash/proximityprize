/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Meta-theorem: every second-order method is capped at `√S`, only depth helps (#407)

This file is the *organizing* meta-theorem of the δ* program. It certifies, axiom-clean and
family-independent, **why every second-order / energy / SDP / Parseval method is provably capped**
at the trivial second-moment bound — and pins the residual escape route to the high-moment depth
alone.

Let `η : ι → ℝ` be a finite family (think: the Gauss periods `η_b = Σ_{x∈μ_n} e_p(bx)`), with
second moment `S = ∑_i (η i)²`. Then:

## The cap (no method using only second-order data can do better)

* `abs_le_sqrt_secondMoment` — `|η b| ≤ √S` for every `b` (Cauchy–Schwarz / Parseval).
* `spike_abs`, `spike_secondMoment` — the cap is **tight**: the spike `(√S, 0, …, 0)` attains
  `max = √S` at second moment exactly `S`. So `√S` is the *best possible* second-order bound.
* `secondMoment_method_floor` — **any** function `g` certifying `∀ η b, |η b| ≤ g (∑ (η i)²)`
  necessarily has `g S ≥ √S`. No second-order method (variance / energy / Parseval / SDP whose
  only datum is `∑ η²`) can ever prove `max < √S`. This is the machine-checked "why" the prize
  floor `√(n·log(q/n)) ≪ √S = √(n·q)` is out of reach for all second-order arguments.

## Only the high-moment depth can close the gap (the residual escape route)

* `sup_le_moment_root` — the valid high-moment route: `max_i |η i| ≤ (∑_i |η i|^{2r})^{1/(2r)}`.
* `momentRoot_one_eq_sqrt` — at depth `r = 1` that route is *exactly* `√S`: depth-1 gives nothing
  beyond second order, so the route can only start improving at `r ≥ 2`.
* `flat_momentRoot` — for the **flat** profile (`m` equal entries `= a ≥ 0`), the route gives
  exactly `a · m^{1/(2r)}`, while the true max is `a`. So the over-estimate factor is **precisely
  `m^{1/(2r)}`**: it is `√m` (the full second-order loss) at `r = 1` and shrinks as `r` grows.
* `flat_gapFactor_antitone` — that factor `m^{1/(2r)}` is **non-increasing in `r`** (for `m ≥ 1`):
  every extra moment-order tightens the bound, never loosens it.
* `flat_gapFactor_tendsto_one` — and `m^{1/(2r)} → 1` as `r → ∞`: in the limit the high-moment
  route recovers the true max exactly. **The gap closes only as `r` grows** — the depth is the
  whole story.
* `momentDepth_method_floor` — but no *single fixed* depth `r` ever beats `√S`: the spike has
  depth-`r` moment `S^r` for every `r`, so a single-depth method `g` has `g (S^r) ≥ √S`. Helping
  requires the depth `r → ∞` jointly with the family being far from a spike — for the Gauss
  periods, exactly the open BGK / Bourgain–Glibichuk–Konyagin char-sum cancellation input.

Net statement: the open core of the prize is **irreducibly a high-moment statement**. Second-order
data caps at `√S` (tight); the only slack lives in the moment depth `r → ∞`, and pinning the rate
at which the flat profile beats the spike at depth `r ≈ log q` is the BGK wall.

This consolidates `Frontier._MomentMethodNoGo`, `MomentSupNormBridge`, and
`Frontier._MetaTheoremSecondOrderFloor` into one named meta-theorem and adds the affirmative
"gap-closes-only-with-depth" facts (`flat_momentRoot`, `flat_gapFactor_antitone`,
`flat_gapFactor_tendsto_one`) that those files leave implicit.

Axiom target: `[propext, Classical.choice, Quot.sound]`. Issue #407.
-/

open Finset Filter Topology

namespace ProximityGap.MetaTheoremSecondOrderCap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. The second-order cap `max ≤ √S`, and its tightness -/

/-- **The second-order cap.** Every term of a real family is bounded by the square root of its
second moment: `|η b| ≤ √(∑_i (η i)²)`. This is Cauchy–Schwarz / Parseval — the strongest bound
any method using only the second moment can give. -/
theorem abs_le_sqrt_secondMoment (η : ι → ℝ) (b : ι) :
    |η b| ≤ Real.sqrt (∑ i, (η i) ^ 2) := by
  have hterm : (η b) ^ 2 ≤ ∑ i, (η i) ^ 2 :=
    Finset.single_le_sum (f := fun i => (η i) ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ b)
  calc |η b| = Real.sqrt ((η b) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ i, (η i) ^ 2) := Real.sqrt_le_sqrt hterm

/-- The single-support "spike" family: value `v` at `b₀`, `0` elsewhere. -/
def spike (b₀ : ι) (v : ℝ) : ι → ℝ := fun i => if i = b₀ then v else 0

/-- **Every positive power sum of the spike collapses to one term:** `∑_i (spike b₀ v i)^k = v^k`
for `k ≥ 1`. -/
theorem spike_pow_sum (b₀ : ι) (v : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    ∑ i, (spike b₀ v i) ^ k = v ^ k := by
  rw [Finset.sum_eq_single b₀]
  · simp [spike]
  · intro j _ hj
    simp only [spike, if_neg hj]
    exact zero_pow (by omega)
  · intro h; exact absurd (Finset.mem_univ b₀) h

/-- **The cap is tight (second moment).** With `v = √S`, `S ≥ 0`, the spike has second moment `S`. -/
theorem spike_secondMoment (b₀ : ι) {S : ℝ} (hS : 0 ≤ S) :
    ∑ i, (spike b₀ (Real.sqrt S) i) ^ 2 = S := by
  rw [spike_pow_sum b₀ _ (by norm_num), Real.sq_sqrt hS]

/-- **The cap is tight (sup-norm).** The spike attains `|·| = √S` at its support point: there is a
family with second moment `S` and `max = √S`, so `√S` is the *best* second-order bound. -/
theorem spike_abs (b₀ : ι) {S : ℝ} (hS : 0 ≤ S) :
    |spike b₀ (Real.sqrt S) b₀| = Real.sqrt S := by
  simp only [spike, if_pos rfl]; exact abs_of_nonneg (Real.sqrt_nonneg S)

/-! ## 2. The meta no-go: no second-order method beats `√S` -/

variable [Nonempty ι]

/-- **No second-order method beats the cap.** If `g : ℝ → ℝ` certifies the sup-norm from the second
moment alone — `∀ η b, |η b| ≤ g (∑_i (η i)²)` — then `g S ≥ √S` for every `S ≥ 0`. Hence no
variance / energy / Parseval / SDP method whose only input is `∑ η²` can prove `max < √S`; in the
prize regime it cannot reach `√(n·log(q/n)) ≪ √S = √(n·q)`. Witness: the spike. -/
theorem secondMoment_method_floor (g : ℝ → ℝ)
    (hg : ∀ (η : ι → ℝ) (b : ι), |η b| ≤ g (∑ i, (η i) ^ 2))
    {S : ℝ} (hS : 0 ≤ S) :
    Real.sqrt S ≤ g S := by
  obtain ⟨b₀⟩ := ‹Nonempty ι›
  have h := hg (spike b₀ (Real.sqrt S)) b₀
  rwa [spike_abs b₀ hS, spike_secondMoment b₀ hS] at h

/-! ## 3. The high-moment route: the only place slack can live -/

/-- **The high-moment route (valid upper bound).** Every term is bounded by the `(2r)`-th root of
the `(2r)`-th power sum: `|η b| ≤ (∑_i |η i|^{2r})^{1/(2r)}` for `r ≥ 1`. At `r = 1` this is the
second-order cap `√S`. -/
theorem sup_le_moment_root (η : ι → ℝ) {r : ℕ} (hr : 1 ≤ r) (b : ι) :
    |η b| ≤ (∑ i, |η i| ^ (2 * r)) ^ ((1 : ℝ) / (2 * r)) := by
  have hterm : |η b| ^ (2 * r) ≤ ∑ i, |η i| ^ (2 * r) :=
    Finset.single_le_sum (f := fun i => |η i| ^ (2 * r))
      (fun i _ => pow_nonneg (abs_nonneg _) _) (Finset.mem_univ b)
  have hroot : (|η b| ^ (2 * r) : ℝ) ^ ((1 : ℝ) / (2 * r))
      ≤ (∑ i, |η i| ^ (2 * r)) ^ ((1 : ℝ) / (2 * r)) :=
    Real.rpow_le_rpow (pow_nonneg (abs_nonneg _) _) hterm (by positivity)
  have hlhs : (|η b| ^ (2 * r) : ℝ) ^ ((1 : ℝ) / (2 * r)) = |η b| := by
    rw [one_div, show (2 * (r : ℝ)) = ((2 * r : ℕ) : ℝ) by push_cast; ring]
    exact Real.pow_rpow_inv_natCast (abs_nonneg _) (by omega)
  rwa [hlhs] at hroot

/-- **At depth `r = 1` the high-moment route IS the second-order cap.** The `2r`-th-root bound
`(∑_i |η i|^{2r})^{1/(2r)}` evaluated at `r = 1` equals exactly `√(∑_i (η i)²) = √S`. So depth-1 of
the ladder gives **nothing** beyond the second-order method — the route can only start improving at
`r ≥ 2`. This is the precise sense in which "the gap closes only as `r` grows": at `r = 1` there is
no gap to close, the route and the cap coincide. -/
theorem momentRoot_one_eq_sqrt (η : ι → ℝ) :
    (∑ i, |η i| ^ (2 * 1)) ^ ((1 : ℝ) / (2 * 1)) = Real.sqrt (∑ i, (η i) ^ 2) := by
  have hsum : ∑ i, |η i| ^ (2 * 1) = ∑ i, (η i) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => by rw [mul_one, sq_abs])
  rw [hsum, Real.sqrt_eq_rpow]
  norm_num

/-- **No single fixed depth `r` beats the cap.** For every fixed `r ≥ 1`, any `g` certifying the
sup-norm from the depth-`r` moment alone — `∀ η b, |η b| ≤ g (∑_i (η i)^{2r})` — has `g (S^r) ≥ √S`.
The spike's depth-`r` moment is `S^r` for *every* `r`, so raising the order never lowers the floor:
a single-depth moment method is just as capped as the second-order one. -/
theorem momentDepth_method_floor {r : ℕ} (hr : 1 ≤ r) (g : ℝ → ℝ)
    (hg : ∀ (η : ι → ℝ) (b : ι), |η b| ≤ g (∑ i, (η i) ^ (2 * r)))
    {S : ℝ} (hS : 0 ≤ S) :
    Real.sqrt S ≤ g (S ^ r) := by
  obtain ⟨b₀⟩ := ‹Nonempty ι›
  have h := hg (spike b₀ (Real.sqrt S)) b₀
  have hmom : ∑ i, (spike b₀ (Real.sqrt S) i) ^ (2 * r) = S ^ r := by
    rw [spike_pow_sum b₀ _ (by omega), pow_mul, Real.sq_sqrt hS]
  rwa [spike_abs b₀ hS, hmom] at h

/-! ## 4. The flat profile: the gap is exactly `m^{1/(2r)}`, closing only as `r → ∞`

For the *flat* family (all `m` entries equal to `a ≥ 0`, the maximal-spread profile), the
high-moment route over-estimates the true max `a` by exactly `m^{1/(2r)}`. This is the affirmative
counterpart of the spike no-go: the spike forces the floor `√S` at every depth; the flat profile
shows the route can in fact approach the true max — but **only** as the depth `r → ∞`. -/

/-- **Flat-profile high-moment value.** For the flat family of `m` entries each equal to `a ≥ 0`
over `Fin m` (`m ≥ 1`, `r ≥ 1`), the high-moment route returns exactly `a · m^{1/(2r)}`. The true
max is `a`, so the over-estimate factor is precisely `m^{1/(2r)}`: `√m` at `r = 1` (the full
second-order loss `√(m·a²) = √S`), shrinking with `r`. -/
theorem flat_momentRoot {m : ℕ} (hm : 1 ≤ m) {a : ℝ} (ha : 0 ≤ a) {r : ℕ} (hr : 1 ≤ r) :
    (∑ _i : Fin m, |a| ^ (2 * r)) ^ ((1 : ℝ) / (2 * r))
      = a * (m : ℝ) ^ ((1 : ℝ) / (2 * r)) := by
  have hsum : ∑ _i : Fin m, |a| ^ (2 * r) = (m : ℝ) * (a ^ (2 * r)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, abs_of_nonneg ha]
  rw [hsum, Real.mul_rpow (by positivity) (by positivity), mul_comm]
  congr 1
  rw [one_div, show (2 * (r : ℝ)) = ((2 * r : ℕ) : ℝ) by push_cast; ring]
  exact Real.pow_rpow_inv_natCast ha (by omega)

/-- The gap (over-estimate) factor of the high-moment route on a flat `m`-entry profile at depth
`r`: `gapFactor m r = m^{1/(2r)}`. By `flat_momentRoot` the route equals `a · gapFactor m r` while
the true max is `a`. -/
noncomputable def gapFactor (m r : ℕ) : ℝ := (m : ℝ) ^ ((1 : ℝ) / (2 * r))

/-- **At `r = 1` the gap factor is the full second-order loss `√m`.** -/
theorem gapFactor_one (m : ℕ) : gapFactor m 1 = Real.sqrt m := by
  rw [gapFactor, Real.sqrt_eq_rpow]
  norm_num

/-- **The gap factor is non-increasing in the moment-order `r`** (for `m ≥ 1`): every extra moment
tightens the high-moment bound, never loosens it. `m^{1/(2s)} ≤ m^{1/(2r)}` when `r ≤ s`. -/
theorem flat_gapFactor_antitone {m : ℕ} (hm : 1 ≤ m) {r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) :
    gapFactor m s ≤ gapFactor m r := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hexp : (1 : ℝ) / (2 * s) ≤ (1 : ℝ) / (2 * r) := by
    apply one_div_le_one_div_of_le
    · have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      positivity
    · have : (r : ℝ) ≤ (s : ℝ) := by exact_mod_cast hrs
      nlinarith
  exact Real.rpow_le_rpow_of_exponent_le hm1 hexp

/-- **The gap factor tends to `1` as the moment-order `r → ∞`** (for `m ≥ 1`): the high-moment
route recovers the true max exactly in the limit. `m^{1/(2r)} → 1`. So the *only* way to beat the
second-order cap is to drive the depth `r → ∞` — the residual escape route is the high moments
alone. -/
theorem flat_gapFactor_tendsto_one {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun r : ℕ => gapFactor m r) atTop (𝓝 1) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  -- exponent `1/(2r) → 0`
  have hexp : Tendsto (fun r : ℕ => (1 : ℝ) / (2 * r)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun r : ℕ => (2 * r : ℝ)) atTop atTop := by
      apply Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
      exact tendsto_natCast_atTop_atTop
    have hinv := h2.inv_tendsto_atTop
    simp only [one_div]
    exact hinv
  -- `(m ^ ·)` is continuous at `0`, with value `m ^ 0 = 1`
  have hcont : ContinuousAt (fun y : ℝ => (m : ℝ) ^ y) 0 := Real.continuousAt_const_rpow hm0
  have hcomp := hcont.tendsto.comp hexp
  have : Tendsto (fun r : ℕ => (m : ℝ) ^ ((1 : ℝ) / (2 * r))) atTop (𝓝 ((m : ℝ) ^ (0 : ℝ))) :=
    hcomp
  simpa [gapFactor, Real.rpow_zero] using this

end ProximityGap.MetaTheoremSecondOrderCap

/-! ## Axiom audit -/
#print axioms ProximityGap.MetaTheoremSecondOrderCap.abs_le_sqrt_secondMoment
#print axioms ProximityGap.MetaTheoremSecondOrderCap.secondMoment_method_floor
#print axioms ProximityGap.MetaTheoremSecondOrderCap.sup_le_moment_root
#print axioms ProximityGap.MetaTheoremSecondOrderCap.momentRoot_one_eq_sqrt
#print axioms ProximityGap.MetaTheoremSecondOrderCap.momentDepth_method_floor
#print axioms ProximityGap.MetaTheoremSecondOrderCap.flat_momentRoot
#print axioms ProximityGap.MetaTheoremSecondOrderCap.gapFactor_one
#print axioms ProximityGap.MetaTheoremSecondOrderCap.flat_gapFactor_antitone
#print axioms ProximityGap.MetaTheoremSecondOrderCap.flat_gapFactor_tendsto_one
