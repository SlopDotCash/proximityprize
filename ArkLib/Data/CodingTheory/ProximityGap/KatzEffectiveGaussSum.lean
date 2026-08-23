/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CumulantGaussPeriodBound

/-!
# The effective-Katz layer for the Gauss-period sup-norm (#407)

The prize core `M(n) = max_{b≠0}‖η_b‖ ≤ √(2n·ln q)` is, by Rojas-León (arXiv:2207.12439, building on
Katz [Kat88, Thm 9.5]), a **theorem in the `q → ∞` limit**: the Gauss sums `G(χ^s)` are jointly
equidistributed / independent (monodromy `= GL(1)^f`, the only relations being Hasse–Davenport), so the
random-phase model is rigorous and `M(n) ≈ √(n·ln q)`.  The prize is the **effective version at fixed
large `q`**: the equidistribution carries a Deligne/Weil discrepancy `≤ conductor · q^{-1/2}`.

This file formalises the *effective consumer*: an explicit **`EffectiveConductorBound`** (the cumulant
deviates from the real-Gaussian/Wick value by at most the geometric Deligne error `K^r · √q`, with `K`
the conductor base of the `r`-fold convolution sheaf) yields the per-frequency bound
`‖η_b‖^{2r} ≤ q·(2r-1)‼·|G|^r + K^r·√q`, hence the worst-case incomplete-sum bound at the scale
`(q·(2r-1)‼·|G|^r + K^r √q)^{1/r}`.  When the geometric error is dominated by the Wick term
(`K^r·√q ≤ q·(2r-1)‼·|G|^r`), this is `≤ (2·q·(2r-1)‼·|G|^r)^{1/r} = 2^{1/r} · M_r`, so the optimum
`r ≈ ln q` still delivers `M ≤ √(2 · 2n · ln q)` (the floor up to the absorbed `2^{1/r} → 1` constant).

The conductor base `K` is the **named open input** — the étale-cohomology estimate (conductor/dimension
of the hypergeometric sheaf whose Frobenius traces are the Gauss sums).  Numerics
(`probe_conductor_prize_regime.py`, `probe_cumulant_prize_regime_healthy.py`) measure `K ≈ 1.28` in the
prize regime `β ≥ 4` (`n/√p → 0`), well inside the budget — but the *proof* that `K = O(1)` there is the
recognized open core, NOT discharged here.

All theorems below are elementary real arithmetic over the proven `cumulant_eq`; **axiom-clean**, no
`sorry`.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound
open ArkLib.ProximityGap.CumulantGaussPeriodBound
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum

namespace ArkLib.ProximityGap.KatzEffectiveGaussSum

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The effective (Katz/Deligne) conductor bound at order `r`.**  The far-frequency mass deviates
from the real-Gaussian (Wick) value by at most the geometric Deligne discrepancy `K^r · √q`, where `K`
is the conductor base of the `r`-fold convolution of the Gauss-sum sheaf:
  `q·E_r − |G|^{2r} ≤ q·(2r-1)‼·|G|^r + K^r·√q`.
This is the *effective* form of Katz's qualitative `q → ∞` independence; `K = O(1)` in the prize regime
is the named open (étale) input. -/
def EffectiveConductorBound (G : Finset F) (r : ℕ) (K : ℝ) : Prop :=
  (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
    ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
      + K ^ r * Real.sqrt (Fintype.card F)

/-- **Single-frequency bound from the effective conductor input.**  For every far frequency `b ≠ 0`,
`‖η_b‖^{2r} ≤ q·(2r-1)‼·|G|^r + K^r·√q`.  Proof: a single far term is `≤` the cumulant
`∑_{b'≠0}‖η_{b'}‖^{2r} = q·E_r − |G|^{2r}` (the proven `cumulant_eq`), then apply the effective bound. -/
theorem eta_pow_le_of_effectiveConductorBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} {r : ℕ} {K : ℝ} (h : EffectiveConductorBound G r K) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        + K ^ r * Real.sqrt (Fintype.card F) := by
  have hmem : b ∈ Finset.univ.erase (0 : F) := Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩
  have hterm : ‖eta ψ G b‖ ^ (2 * r)
      ≤ ∑ b' ∈ Finset.univ.erase (0 : F), ‖eta ψ G b'‖ ^ (2 * r) :=
    Finset.single_le_sum (f := fun b' : F => ‖eta ψ G b'‖ ^ (2 * r))
      (fun i _ => by positivity) hmem
  rw [cumulant_eq hψ G r] at hterm
  calc ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) := hterm
    _ ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
          + K ^ r * Real.sqrt (Fintype.card F) := h
    _ = (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
          + K ^ r * Real.sqrt (Fintype.card F) := by ring

/-- **The effective worst-case incomplete-sum bound (#407).**  `EffectiveConductorBound` at order
`r ≥ 1` discharges `WorstCaseIncompleteSumBound` at the scale
`X_r = (q·(2r-1)‼·|G|^r + K^r·√q)^{1/r}` — the effective Katz/Deligne analogue of
`worstCaseIncompleteSumBound_of_cumulantBound`, but from the explicit conductor input rather than the
exact sub-Wick hypothesis.  Minimising `X_r` over `r` (optimum `r* ≈ ln q`, where the geometric error
`K^r √q` is dominated by the Wick term for `K = O(1)`) yields the `√(2n ln q)` per-frequency target up
to the constant `2^{1/r} → 1`. -/
theorem worstCaseIncompleteSumBound_of_effectiveConductorBound {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ} {K : ℝ} (hr : 1 ≤ r)
    (h : EffectiveConductorBound G r K) :
    WorstCaseIncompleteSumBound ψ G
      (((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        + K ^ r * Real.sqrt (Fintype.card F)) ^ ((r : ℝ)⁻¹)) := by
  intro b hb
  set X : ℝ := (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
    + K ^ r * Real.sqrt (Fintype.card F) with hX
  have hpow : (‖eta ψ G b‖ ^ 2) ^ r ≤ X := by
    rw [← pow_mul]; exact eta_pow_le_of_effectiveConductorBound hψ h hb
  calc ‖eta ψ G b‖ ^ 2
      = ((‖eta ψ G b‖ ^ 2) ^ r) ^ ((r : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (sq_nonneg _) (Nat.one_le_iff_ne_zero.mp hr)).symm
    _ ≤ X ^ ((r : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) hpow (by positivity)

omit [DecidableEq F] in
/-- **The effective consumer collapses to the cumulant scale when the Deligne error is absorbed.**
If the geometric error `K^r·√q` is dominated by the Wick term, the effective scale
`(Wick + K^r√q)^{1/r}` is `≤ (2·Wick)^{1/r} = 2^{1/r}·Wick^{1/r}` — i.e. the same `M_r` scale as the
cumulant consumer up to the constant `2^{1/r}` (which `→ 1` at the optimum `r ≈ ln q`).  This makes the
"`K = O(1)` ⟹ prize floor" reduction explicit and quantitative. -/
theorem effective_scale_le_two_mul_wick {G : Finset F} {r : ℕ} {K : ℝ} (hr : 1 ≤ r) (hK : 0 ≤ K)
    (habsorb : K ^ r * Real.sqrt (Fintype.card F)
      ≤ (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :
    ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        + K ^ r * Real.sqrt (Fintype.card F)) ^ ((r : ℝ)⁻¹)
      ≤ (2 * ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))
          ^ ((r : ℝ)⁻¹) := by
  have hbase : 0 ≤ (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
      + K ^ r * Real.sqrt (Fintype.card F) := by positivity
  apply Real.rpow_le_rpow hbase _ (by positivity)
  linarith [habsorb]

end ArkLib.ProximityGap.KatzEffectiveGaussSum

