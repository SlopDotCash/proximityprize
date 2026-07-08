/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.NumberTheory.JacobiSum.Basic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R26BoundedResidual
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R26ResidualL2CrossIdentity
import ArkLib.Data.CodingTheory.ProximityGap.ConstantIndexGaussSumBound

/-!
# R27F (#466 round 27, MIXED lane): the Main–Res mixed moment is a REAL quartic problem

## The discovery (probe `probe_r27f_mixed_moment.py`, exact cells up to `p = 65537`)

Round 26 pinned the subfamily gate's open content as Main–Res mixed-moment cancellation:
`m·I_H(s₀) = M'(s₀) + Res(s₀)` with `M' = -n + Main_Y`, and every per-part split of
`∑‖I_H‖⁴` overspends the Wick budget even though the true rung ratio is ≈ 0.87.

**New exact structure (this round).**  In the rung regime (`χ'(-1) = 1` for the whole
family, i.e. `2m ∣ q−1` — true at every probed cell) BOTH `M'(s₀)` and `Res(s₀)` are
pointwise REAL.  Probe: `max |Im M'| = max |Im Res| = 0.0` exactly at
`(p,n,m,d) ∈ {(97,8,16,8), (193,8,16,8), (257,8,16,4), (1153,8,16,8)}`.  Mechanism
(proved below): the family is inversion-closed, `conj T_{χ'} = T_{χ'⁻¹}` and
`conj g(χ') = g(χ'⁻¹)` when `χ'(-1) = 1`, so each sum is fixed by conjugation.

Consequently the mixed-moment problem is REAL bookkeeping of `∑ (A + B)⁴` with
`A = M'.re`, `B = Res.re`; the cross term `c = M'·conj Res = A·B` is real with
`c² = ‖M'‖²·‖Res‖²` **pointwise** (probe: `Src2/Sc2 = 1.0000`, `Sab = Sc2` at all cells).

## The measured budget decomposition (flagship cell `p=65537, n=8, m=16, d=8, m'=2`)

With budget `= m⁴·3q·Σ²` (rung ratio `m⁴S₂ᴰ/budget = 0.8733`):

| term          | fraction of budget |
|---------------|--------------------|
| `∑A⁴`         | 0.0036             |
| `∑B⁴`         | 0.7635 (AT Wick: `∑B⁴/3q(Mnq)² = 1.00`) |
| `6∑A²B²`      | 0.1116             |
| `4∑(A³B+AB³)` | −0.0054 (odd term → 0 at large q; +0.08..0.11 at small q) |

**The resisting object is exactly `∑A²B²`**: its Cauchy–Schwarz bound
`√(∑A⁴·∑B⁴)` is off by the stable factor `∑A²B²/CS ≈ 0.33–0.49` (0.356 at the
flagship), and CS-composed bookkeeping gives 1.37–1.57× the budget while the true
total is 0.87.  Closure requires `κ`-improved CS with:
* `κ ≤ 0.74` at `m' = 2` (measured 0.356),
* `κ ≤ 0.50` at `m' = 4` (measured 0.347) — `κ = 1/2` is the calibrated target,
plus the odd-term bound `Θ` (measured `|odd| ≤ 0.114·budget/4`, → 0 as `q → ∞`).

## What is PROVEN here (axiom-clean)

1. `conj_twistedThinSum`, `conj_gaussSum_of_even`: the conjugation dictionary.
2. `sum_im_eq_zero_of_inv_closed` + `chiSubfamilyResidual_im_eq_zero`: the residual
   (and by the same lemma any inversion-closed `g·T` sum, e.g. `Main_Y`) is REAL in
   the even regime — the round's exact structural theorem.
3. `quartic_expansion`, `mixed_sq_le_sqrt_quartics`: the exact real expansion and
   the CS face for the mixed term.
4. `sum_quartic_le_of_mixed_half_cs` + `sum_norm_quartic_le_of_mixed_faces`: the
   COMPOSED rung bookkeeping — given the two faces `∑A⁴ ≤ Ea`, `∑B⁴ ≤ Eb`, the named
   mixed bound at ratio `κ` and the named odd bound `Θ`, the full quartic sum is
   `≤ Ea + Eb + 6κ√(Ea·Eb) + 4Θ`; if that fits under the budget, the rung fires.

## What remains OPEN (named, probe-calibrated — NO closure claimed)

* `MixedMainResHalfCS S A B κ` at `κ = 1/2`: `∑A²B² ≤ κ·√(∑A⁴)·√(∑B⁴)` for the
  concrete Main/Res pair — a genuine 4-character object
  (`∑_{s₀} T_a conj T_b T_c conj T_d`, a,b ∈ Y-side, c,d ∈ complement) needing its
  own Weil-family input; the r26 SECOND-moment cross-χ identity does not reach it.
* `OddMainResBound S A B Θ` with `Θ = o(budget)`: the signed odd moment
  `∑(A²+B²)AB = ∑ ±(A²+B²)√(A²B²)` — sign equidistribution, measured → 0.

Axiom-clean target (`propext, Classical.choice, Quot.sound`).  Issue #466, round 27.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open Finset
open ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung
open ArkLib.ProximityGap.Frontier.R19ChiDecomposition
open ArkLib.ProximityGap.Frontier.R19ExplicitCharacterRung
open ArkLib.ProximityGap.Frontier.R26BoundedResidual

namespace ArkLib.ProximityGap.Frontier.R27FMixedMoment

local notation "conj'" => starRingEnd ℂ

/-! ## 1. The real quartic layer: exact expansion and the CS face -/

section RealLayer

variable {ι : Type*}

/-- **Exact quartic expansion** of the rung sum `∑ (A+B)⁴` into the two faces, the
mixed even term, and the odd terms.  This is the m⁴·S₂ᴰ bookkeeping identity once
Main′ and Res are known to be real (§3). -/
theorem quartic_expansion (S : Finset ι) (A B : ι → ℝ) :
    ∑ s ∈ S, (A s + B s) ^ 4
      = ∑ s ∈ S, (A s) ^ 4 + 4 * ∑ s ∈ S, (A s) ^ 3 * B s
        + 6 * ∑ s ∈ S, (A s) ^ 2 * (B s) ^ 2
        + 4 * ∑ s ∈ S, A s * (B s) ^ 3 + ∑ s ∈ S, (B s) ^ 4 := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- The Cauchy–Schwarz face for the mixed even term:
`∑ A²B² ≤ √(∑A⁴)·√(∑B⁴)`.  The probes measure the true ratio at 0.33–0.49 —
this face alone overspends; the open content is the `κ`-improvement below. -/
theorem mixed_sq_le_sqrt_quartics (S : Finset ι) (A B : ι → ℝ) :
    ∑ s ∈ S, (A s) ^ 2 * (B s) ^ 2
      ≤ Real.sqrt (∑ s ∈ S, (A s) ^ 4) * Real.sqrt (∑ s ∈ S, (B s) ^ 4) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt S (fun s => (A s) ^ 2) (fun s => (B s) ^ 2)
  have h4 : ∀ (x : ℝ), (x ^ 2) ^ 2 = x ^ 4 := fun x => by ring
  simpa only [h4] using h

/-- **The named OPEN mixed-moment bound** (`κ`-improved Cauchy–Schwarz).
Probe calibration: measured `κ` is 0.33–0.49 across all exact cells (0.356 at the
flagship `p = 65537, m' = 2`); the rung fires with `κ = 1/2` at `m' = 4` and with
`κ = 3/4` at `m' = 2`.  This is a genuine 4-character object (`T_a conj T_b T_c
conj T_d` across the Y/complement split) — NOT reachable from the r26 second-moment
cross-χ identity; it needs its own Weil-family input. -/
def MixedMainResHalfCS (S : Finset ι) (A B : ι → ℝ) (κ : ℝ) : Prop :=
  ∑ s ∈ S, (A s) ^ 2 * (B s) ^ 2
    ≤ κ * (Real.sqrt (∑ s ∈ S, (A s) ^ 4) * Real.sqrt (∑ s ∈ S, (B s) ^ 4))

/-- **The named OPEN odd-moment bound**: the signed object `∑ (A³B + AB³)`.
Probe: −0.0054·budget/4 at the flagship (essentially zero; sign-equidistributed),
+0.08..0.11·budget/4 at small cells.  Needs `Θ = o(budget)`. -/
def OddMainResBound (S : Finset ι) (A B : ι → ℝ) (Θ : ℝ) : Prop :=
  |∑ s ∈ S, ((A s) ^ 3 * B s + A s * (B s) ^ 3)| ≤ Θ

/-- **The composed refined bookkeeping**: faces + `κ`-mixed + odd give
`∑(A+B)⁴ ≤ Ea + Eb + 6κ√(Ea·Eb) + 4Θ`.  At the flagship cell with the true faces
this evaluates to `0.767 + 6κ·0.0524 + 4Θ` of budget — under budget for `κ ≤ 0.74`. -/
theorem sum_quartic_le_of_mixed_half_cs (S : Finset ι) (A B : ι → ℝ)
    {Ea Eb Θ κ : ℝ} (hκ : 0 ≤ κ)
    (hA : ∑ s ∈ S, (A s) ^ 4 ≤ Ea) (hB : ∑ s ∈ S, (B s) ^ 4 ≤ Eb)
    (hM : MixedMainResHalfCS S A B κ) (hO : OddMainResBound S A B Θ) :
    ∑ s ∈ S, (A s + B s) ^ 4 ≤ Ea + Eb + 6 * κ * Real.sqrt (Ea * Eb) + 4 * Θ := by
  have hA0 : (0 : ℝ) ≤ ∑ s ∈ S, (A s) ^ 4 :=
    Finset.sum_nonneg fun s _ => by positivity
  have hB0 : (0 : ℝ) ≤ ∑ s ∈ S, (B s) ^ 4 :=
    Finset.sum_nonneg fun s _ => by positivity
  have hEa0 : (0 : ℝ) ≤ Ea := hA0.trans hA
  have hEb0 : (0 : ℝ) ≤ Eb := hB0.trans hB
  -- the mixed term against the face budgets
  have hsqrt : Real.sqrt (∑ s ∈ S, (A s) ^ 4) * Real.sqrt (∑ s ∈ S, (B s) ^ 4)
      ≤ Real.sqrt (Ea * Eb) := by
    rw [Real.sqrt_mul hEa0]
    exact mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hmix : ∑ s ∈ S, (A s) ^ 2 * (B s) ^ 2 ≤ κ * Real.sqrt (Ea * Eb) :=
    hM.trans (mul_le_mul_of_nonneg_left hsqrt hκ)
  -- the odd term against Θ
  have hodd : ∑ s ∈ S, ((A s) ^ 3 * B s + A s * (B s) ^ 3) ≤ Θ :=
    (le_abs_self _).trans hO
  -- split the odd sum into the two expansion terms
  have hsplit : ∑ s ∈ S, ((A s) ^ 3 * B s + A s * (B s) ^ 3)
      = ∑ s ∈ S, (A s) ^ 3 * B s + ∑ s ∈ S, A s * (B s) ^ 3 :=
    Finset.sum_add_distrib
  rw [quartic_expansion]
  have h1 : 4 * ∑ s ∈ S, (A s) ^ 3 * B s + 4 * ∑ s ∈ S, A s * (B s) ^ 3 ≤ 4 * Θ := by
    have := hodd
    rw [hsplit] at this
    linarith
  have h2 : 6 * ∑ s ∈ S, (A s) ^ 2 * (B s) ^ 2 ≤ 6 * (κ * Real.sqrt (Ea * Eb)) := by
    linarith
  linarith

end RealLayer

/-! ## 2. The conjugation dictionary for the concrete objects -/

section ConjDictionary

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable local instance : DecidableEq (MulChar F ℂ) := Classical.decEq _

/-- Conjugation sends the thin twisted sum of `χ'` to that of `χ'⁻¹` (exactly — no
regime hypothesis needed). -/
theorem conj_twistedThinSum (χ' : MulChar F ℂ) (G : Finset F) (t : F) :
    conj' (twistedThinSum χ' G t) = twistedThinSum χ'⁻¹ G t := by
  unfold twistedThinSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.conj_conj, conj_mulChar, inv_inv]

/-- In the even regime `χ'(-1) = 1` (true for the whole rung family when
`2m ∣ q−1`), conjugation sends `g(χ', ψ)` to `g(χ'⁻¹, ψ)` with NO phase. -/
theorem conj_gaussSum_of_even {χ' : MulChar F ℂ} (ψ : AddChar F ℂ)
    (h : χ' (-1) = 1) :
    conj' (gaussSum χ' ψ) = gaussSum χ'⁻¹ ψ := by
  rw [ArkLib.ProximityGap.ConstantIndexGaussSum.conj_gaussSum]
  have h2 : χ'⁻¹ (-1) = 1 := by
    rw [MulChar.inv_apply']
    simpa using h
  rw [← mul_gaussSum_inv_eq_gaussSum χ'⁻¹ ψ, h2, one_mul]

/-- **Generic realness by inversion pairing**: a sum of `f` over an
inversion-closed character family with `conj (f χ') = f χ'⁻¹` is real. -/
theorem sum_im_eq_zero_of_inv_closed (Ω : Finset (MulChar F ℂ))
    (f : MulChar F ℂ → ℂ)
    (hinv : ∀ χ' ∈ Ω, χ'⁻¹ ∈ Ω)
    (hconj : ∀ χ' ∈ Ω, conj' (f χ') = f χ'⁻¹) :
    (∑ χ' ∈ Ω, f χ').im = 0 := by
  have hself : conj' (∑ χ' ∈ Ω, f χ') = ∑ χ' ∈ Ω, f χ' := by
    rw [map_sum, Finset.sum_congr rfl hconj]
    exact Finset.sum_nbij' (fun χ' => χ'⁻¹) (fun χ' => χ'⁻¹) hinv hinv
      (fun a _ => inv_inv a) (fun a _ => inv_inv a) (fun a _ => rfl)
  exact Complex.conj_eq_iff_im.mp hself

/-- **THE ROUND'S EXACT STRUCTURAL THEOREM**: the omitted-character residual
`Res(s₀) = ∑_{χ' ∈ chiFamily χ \ Y} g(χ')·T_{χ'}(s₀)` is pointwise REAL whenever the
omitted family is inversion-closed and even (`χ'(-1) = 1`).  Both hypotheses hold in
the rung regime (`Y = chiFamily (χ^d)`, `2m ∣ q−1`); the probes confirm
`max |Im Res| = 0.0` exactly.  The same lemma applied to `Y`-side terms makes
`Main_Y(s₀)` (and hence `M' = -n + Main_Y`) real, so the whole mixed-moment problem
descends to the REAL quartic layer of §1. -/
theorem chiSubfamilyResidual_im_eq_zero (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (G : Finset F) (Y : Finset (MulChar F ℂ)) (s₀ : F)
    (hinv : ∀ χ' ∈ chiFamily χ \ Y, χ'⁻¹ ∈ chiFamily χ \ Y)
    (heven : ∀ χ' ∈ chiFamily χ \ Y, χ' (-1) = 1) :
    (chiSubfamilyResidual χ ψ G Y s₀).im = 0 := by
  unfold chiSubfamilyResidual
  refine sum_im_eq_zero_of_inv_closed _ _ hinv fun χ' hχ' => ?_
  rw [map_mul, conj_twistedThinSum]
  rw [conj_gaussSum_of_even ψ (heven χ' hχ')]

end ConjDictionary

/-! ## 3. The bridge: real parts carry the full quartic sum -/

section Bridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- For a real complex number, the norm fourth power is the real-part fourth power. -/
theorem norm_pow_four_of_im_zero (z : ℂ) (hz : z.im = 0) :
    ‖z‖ ^ 4 = z.re ^ 4 := by
  have h2 : ‖z‖ ^ 2 = z.re ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hz]
    ring
  calc ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 := by ring
    _ = (z.re ^ 2) ^ 2 := by rw [h2]
    _ = z.re ^ 4 := by ring

/-- **The composed rung bookkeeping over ℂ**: if `M'` and `Res` are pointwise real
on `S` (§2), the faces are budgeted (`∑‖M'‖⁴ ≤ Ea` — proven tiny; `∑‖Res‖⁴ ≤ Eb` —
the Wick-scale face), and the two NAMED OPEN bounds hold, then the full rung sum
`∑ ‖M' + Res‖⁴` fits under any budget dominating
`Ea + Eb + 6κ√(Ea·Eb) + 4Θ`.  Flagship calibration: with the true faces the
left side is 0.873·budget while this bound gives ≤ 1·budget for `κ ≤ 0.74`
(`m' = 2`) resp. `κ ≤ 0.50` (`m' = 4`). -/
theorem sum_norm_quartic_le_of_mixed_faces (S : Finset F) (Mp Rv : F → ℂ)
    (hMim : ∀ s ∈ S, (Mp s).im = 0) (hRim : ∀ s ∈ S, (Rv s).im = 0)
    {Ea Eb Θ κ Budget : ℝ} (hκ : 0 ≤ κ)
    (hA : ∑ s ∈ S, ‖Mp s‖ ^ 4 ≤ Ea) (hB : ∑ s ∈ S, ‖Rv s‖ ^ 4 ≤ Eb)
    (hM : MixedMainResHalfCS S (fun s => (Mp s).re) (fun s => (Rv s).re) κ)
    (hO : OddMainResBound S (fun s => (Mp s).re) (fun s => (Rv s).re) Θ)
    (hfit : Ea + Eb + 6 * κ * Real.sqrt (Ea * Eb) + 4 * Θ ≤ Budget) :
    ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4 ≤ Budget := by
  have hres : ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4
      = ∑ s ∈ S, ((Mp s).re + (Rv s).re) ^ 4 := by
    refine Finset.sum_congr rfl fun s hs => ?_
    have him : (Mp s + Rv s).im = 0 := by
      rw [Complex.add_im, hMim s hs, hRim s hs, add_zero]
    rw [norm_pow_four_of_im_zero _ him, Complex.add_re]
  have hA' : ∑ s ∈ S, ((Mp s).re) ^ 4 ≤ Ea := by
    refine le_trans (le_of_eq ?_) hA
    exact Finset.sum_congr rfl fun s hs =>
      (norm_pow_four_of_im_zero _ (hMim s hs)).symm
  have hB' : ∑ s ∈ S, ((Rv s).re) ^ 4 ≤ Eb := by
    refine le_trans (le_of_eq ?_) hB
    exact Finset.sum_congr rfl fun s hs =>
      (norm_pow_four_of_im_zero _ (hRim s hs)).symm
  rw [hres]
  exact le_trans
    (sum_quartic_le_of_mixed_half_cs S _ _ hκ hA' hB' hM hO) hfit

end Bridge

end ArkLib.ProximityGap.Frontier.R27FMixedMoment

-- Honesty audit (axiom-clean target: propext, Classical.choice, Quot.sound)
#print axioms ArkLib.ProximityGap.Frontier.R27FMixedMoment.quartic_expansion
#print axioms ArkLib.ProximityGap.Frontier.R27FMixedMoment.mixed_sq_le_sqrt_quartics
#print axioms ArkLib.ProximityGap.Frontier.R27FMixedMoment.sum_quartic_le_of_mixed_half_cs
#print axioms ArkLib.ProximityGap.Frontier.R27FMixedMoment.conj_twistedThinSum
#print axioms ArkLib.ProximityGap.Frontier.R27FMixedMoment.conj_gaussSum_of_even
#print axioms ArkLib.ProximityGap.Frontier.R27FMixedMoment.sum_im_eq_zero_of_inv_closed
#print axioms ArkLib.ProximityGap.Frontier.R27FMixedMoment.chiSubfamilyResidual_im_eq_zero
#print axioms ArkLib.ProximityGap.Frontier.R27FMixedMoment.norm_pow_four_of_im_zero
#print axioms ArkLib.ProximityGap.Frontier.R27FMixedMoment.sum_norm_quartic_le_of_mixed_faces
