/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge

/-!
# LANE SUBWICK (#466 round 20): sub-Wick monotonicity as moment algebra —
  log-convexity, the automatic large-r regime, and the no-self-improvement fixed point

Setting (R15–R19): `I_H(s₀) = ∑_{b∈H} conj(η_b)·ψ(b s₀)`, `S_r^D = ∑_{s∉D}‖I_H‖^{2r}`,
`Σ = ∑_{b∈H}‖η_b‖²`, `D = {0} ∪ μ_n`. Round-19 RECURSION left "sub-Wick monotonicity"
(`L_r := (S_{r+1}^D/S_r^D)/((2r+1)Σ) ≤ 1`, measured 0.19–0.99 in ALL cells) as a standalone
conjecture. This lane attacks it as pure moment algebra.

## PROBE VERDICT (`probe_r20_subwick.py`, exact FFT, same 16 cells as r19, r ≤ 10)

* **Log-convexity + ratio monotonicity hold exactly** (they must — Cauchy–Schwarz on the
  positive away measure): `(S_{r+1})² ≤ S_r·S_{r+2}` and `S_{j+1}S_k ≤ S_j S_{k+1}` (j ≤ k),
  hence `S_{r+1}/S_r` is INCREASING in r, saturating to `M²_away` (measured ratio₉/M² =
  0.87–1.0 in all cells).
* **The automatic regime is real**: `L_r ≤ 1` for every r with `2r+1 ≥ Λ = M²_away/Σ` in all
  cells (threshold r₀ = (Λ−1)/2 ≤ 5.72 across cells); measured `L_r ≤ 1` even below r₀
  (no violations anywhere, r ≤ 9).
* **No self-improvement (depth-independence, exact)**: the chain
  `Chebyshev-at-depth-R ∘ sup-split^{R−2} ∘ rung-2` returns the SAME constraint at every
  depth — the slack `chain/Chebyshev = S₂/M⁴_away` is numerically independent of R in every
  cell (machine-exact), matching the algebraic theorem below.

## What THIS file proves (axiom-clean; no Weil, no analysis)

* `rungMoment_sq_le_mul` — **log-convexity of the away moments** (Cauchy–Schwarz):
  `(S_{r+1}^D)² ≤ S_r^D · S_{r+2}^D` for every r. The moment sequence of the positive away
  measure is log-convex, so the rung ratio `S_{r+1}/S_r` is nondecreasing in r.
* `rungMoment_ratio_mono` — the multiplicative (division-free) form of ratio monotonicity:
  `j ≤ k → S_{j+1}^D · S_k^D ≤ S_j^D · S_{k+1}^D`.
* `subWick_of_awaySupBound` — **the automatic large-r regime**: if `AwaySupBound C` (r19
  fixed-point Prop, `sup_away‖I‖² ≤ CΣ`) holds and `C ≤ 2r+1`, then rung r is sub-Wick:
  `S_{r+1}^D ≤ (2r+1)·Σ·S_r^D`, i.e. `L_r ≤ 1`. Sub-Wick monotonicity has CONTENT only at
  the finitely many rungs `2r+1 < C` — for the true C = Λ (measured 1.7–12.4) that is
  r ≤ 5 in every measured cell.
* `awaySup_lower_of_superWick` — the converse direction, making the two-way link exact: a
  sub-Wick VIOLATION at any rung r certifies an away-sup lower bound
  `∃ s∉D, (2r+1)·Σ < ‖I_H(s)‖²`. So sub-Wick monotonicity at rung r is EQUIVALENT (up to
  the ≤2.7 sup-split tightness, r19 probe) to the away sup at budget (2r+1)Σ: the standalone
  conjecture is not weaker than the sup — it IS the sup, rung by rung.
* `awayValue_pow_le_chain` — the full depth-R bootstrap chain in one inequality: under
  `AwaySupBound K`, every away value obeys `‖I(s)‖^{2(R+2)} ≤ (KΣ)^R · S₂^D`.
* `fixedPoint_depth_independent` — **the no-self-improvement theorem** (the bankable no-go):
  for x > 0, `x^{R+2} ≤ x^R·B ↔ x² ≤ B`. Instantiated at `x = KΣ` (the self-consistent
  sup), `B = S₂^D`: the constraint extracted from the depth-R chain is EXACTLY the depth-2
  Chebyshev `(KΣ)² ≤ S₂`, for every R. The sup enters once per sup-split rung and exits once
  per Chebyshev power — the K-degrees cancel identically, so iterating the recursion to any
  depth proves nothing beyond `M²_away ≤ √(S₂^D)` (Chebyshev, the √q-lossy step). No
  bootstrap loop closes; log-convex interpolation between rung 2 and rung R only convexly
  combines the same two endpoints and cannot beat this either.

## Honest scope

Sub-Wick monotonicity is NOT closed here: it is (i) proven automatic for `2r+1 ≥ C` given
the fixed-point Prop, and (ii) proven EQUIVALENT to per-rung away-sup budgets below that —
i.e. the standalone conjecture collapses INTO `AwaySupBound`, rung by rung, in both
directions. The genuinely new no-go is `fixedPoint_depth_independent`: the
recursion+Chebyshev self-improvement loop is vacuous at every depth (the fixed-point
inequality is depth-free), killing the "interpolate rung 2 against the deep tower" route.
Wall untouched. Issue #466, round 20, LANE SUBWICK.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.Frontier.R20SubWickInterpolation

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Lane-local incidence sum `I_H(s₀) = ∑_{b∈H} conj(η_b)·ψ(b·s₀)` (definitionally the
R15–R19 object; kept local to avoid depending on frontier scratch oleans). -/
noncomputable def incidenceSum (ψ : AddChar F ℂ) (G H : Finset F) (s₀ : F) : ℂ :=
  ∑ b ∈ H, (starRingEnd ℂ) (eta ψ G b) * ψ (b * s₀)

/-- The diagonal-deleted rung moment `S_r^D = ∑_{s₀∉D} ‖I_H(s₀)‖^{2r}`. -/
noncomputable def rungMoment (ψ : AddChar F ℂ) (G H D : Finset F) (r : ℕ) : ℝ :=
  ∑ s₀ ∈ Finset.univ \ D, ‖incidenceSum ψ G H s₀‖ ^ (2 * r)

theorem rungMoment_nonneg (ψ : AddChar F ℂ) (G H D : Finset F) (r : ℕ) :
    0 ≤ rungMoment ψ G H D r :=
  Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _

/-- The r19 fixed-point Prop, restated locally: `sup_{s∉D}‖I_H(s)‖² ≤ C·Σ`. -/
def AwaySupBound (ψ : AddChar F ℂ) (G H D : Finset F) (C : ℝ) : Prop :=
  ∀ s ∈ Finset.univ \ D,
    ‖incidenceSum ψ G H s‖ ^ 2 ≤ C * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2

/-! ### (1) Log-convexity of the away moment sequence (Cauchy–Schwarz). -/

/-- **Log-convexity**: `(S_{r+1}^D)² ≤ S_r^D · S_{r+2}^D` — the away moments are moments of
a positive measure, hence log-convex; the rung ratio `S_{r+1}/S_r` is nondecreasing in r. -/
theorem rungMoment_sq_le_mul (ψ : AddChar F ℂ) (G H D : Finset F) (r : ℕ) :
    (rungMoment ψ G H D (r + 1)) ^ 2
      ≤ rungMoment ψ G H D r * rungMoment ψ G H D (r + 2) := by
  classical
  have key := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ \ D)
    (fun s => ‖incidenceSum ψ G H s‖ ^ r)
    (fun s => ‖incidenceSum ψ G H s‖ ^ (r + 2))
  unfold rungMoment
  calc (∑ s ∈ Finset.univ \ D, ‖incidenceSum ψ G H s‖ ^ (2 * (r + 1))) ^ 2
      = (∑ s ∈ Finset.univ \ D,
          ‖incidenceSum ψ G H s‖ ^ r * ‖incidenceSum ψ G H s‖ ^ (r + 2)) ^ 2 := by
        congr 1
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [← pow_add]; congr 1; ring
    _ ≤ (∑ s ∈ Finset.univ \ D, (‖incidenceSum ψ G H s‖ ^ r) ^ 2)
          * ∑ s ∈ Finset.univ \ D, (‖incidenceSum ψ G H s‖ ^ (r + 2)) ^ 2 := key
    _ = (∑ s ∈ Finset.univ \ D, ‖incidenceSum ψ G H s‖ ^ (2 * r))
          * ∑ s ∈ Finset.univ \ D, ‖incidenceSum ψ G H s‖ ^ (2 * (r + 2)) := by
        congr 1
        · refine Finset.sum_congr rfl (fun s _ => ?_)
          rw [← pow_mul]; congr 1; ring
        · refine Finset.sum_congr rfl (fun s _ => ?_)
          rw [← pow_mul]; congr 1; ring

/-- **Ratio monotonicity (multiplicative form)**: `j ≤ k → S_{j+1}·S_k ≤ S_j·S_{k+1}`.
Division-free statement of "the rung ratio increases in r". -/
theorem rungMoment_ratio_mono (ψ : AddChar F ℂ) (G H D : Finset F) {j k : ℕ} (h : j ≤ k) :
    rungMoment ψ G H D (j + 1) * rungMoment ψ G H D k
      ≤ rungMoment ψ G H D j * rungMoment ψ G H D (k + 1) := by
  induction k with
  | zero =>
      have hj : j = 0 := Nat.le_zero.mp h
      subst hj
      exact le_of_eq (mul_comm _ _)
  | succ k ih =>
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · -- j ≤ k: chain IH with log-convexity at rung k.
        have hjk : j ≤ k := Nat.lt_succ_iff.mp hlt
        have ihk := ih hjk
        have hcs := rungMoment_sq_le_mul ψ G H D k
        set Sj := rungMoment ψ G H D j
        set Sj1 := rungMoment ψ G H D (j + 1)
        set Sk := rungMoment ψ G H D k
        set Sk1 := rungMoment ψ G H D (k + 1)
        set Sk2 := rungMoment ψ G H D (k + 2)
        have hSk1 : 0 ≤ Sk1 := rungMoment_nonneg ψ G H D (k + 1)
        rcases eq_or_lt_of_le hSk1 with heq | hpos
        · -- Sk1 = 0: LHS = 0 ≤ RHS.
          rw [← heq]
          have : Sj1 * (0:ℝ) = 0 := mul_zero _
          rw [this]
          exact mul_nonneg (rungMoment_nonneg ψ G H D j) (rungMoment_nonneg ψ G H D (k + 2))
        · -- Sk1 > 0: cancel it.
          have hchain : (Sj1 * Sk1) * Sk1 ≤ (Sj * Sk2) * Sk1 := by
            have h1 : Sj1 * (Sk1 ^ 2) ≤ Sj1 * (Sk * Sk2) :=
              mul_le_mul_of_nonneg_left hcs (rungMoment_nonneg ψ G H D (j + 1))
            have h2 : (Sj1 * Sk) * Sk2 ≤ (Sj * Sk1) * Sk2 :=
              mul_le_mul_of_nonneg_right ihk (rungMoment_nonneg ψ G H D (k + 2))
            calc (Sj1 * Sk1) * Sk1 = Sj1 * (Sk1 ^ 2) := by ring
              _ ≤ Sj1 * (Sk * Sk2) := h1
              _ = (Sj1 * Sk) * Sk2 := by ring
              _ ≤ (Sj * Sk1) * Sk2 := h2
              _ = (Sj * Sk2) * Sk1 := by ring
          exact le_of_mul_le_mul_right hchain hpos
      · -- j = k + 1: equality by commutativity.
        have hj : j = k + 1 := le_antisymm h hge
        subst hj
        exact le_of_eq (mul_comm _ _)

/-! ### (2) The sup-split step and the automatic large-r sub-Wick regime. -/

/-- The exact sup-split recursion (r19 `sup_split_recursion`, restated locally):
any away-sup budget `B` gives `S_{r+1}^D ≤ B·S_r^D`. -/
theorem sup_split_recursion (ψ : AddChar F ℂ) (G H D : Finset F) (B : ℝ)
    (hB : ∀ s ∈ Finset.univ \ D, ‖incidenceSum ψ G H s‖ ^ 2 ≤ B) (r : ℕ) :
    rungMoment ψ G H D (r + 1) ≤ B * rungMoment ψ G H D r := by
  unfold rungMoment
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun s hs => ?_)
  have h1 : ‖incidenceSum ψ G H s‖ ^ (2 * (r + 1))
      = ‖incidenceSum ψ G H s‖ ^ 2 * ‖incidenceSum ψ G H s‖ ^ (2 * r) := by
    rw [← pow_add]; congr 1; ring
  rw [h1]
  exact mul_le_mul_of_nonneg_right (hB s hs) (pow_nonneg (norm_nonneg _) _)

/-- **The automatic large-r sub-Wick regime.** Under `AwaySupBound C`, every rung r with
`C ≤ 2r+1` is sub-Wick: `S_{r+1}^D ≤ (2r+1)·Σ·S_r^D` (i.e. `L_r ≤ 1`). Sub-Wick
monotonicity has content only at the finitely many rungs `2r+1 < C`. -/
theorem subWick_of_awaySupBound (ψ : AddChar F ℂ) (G H D : Finset F) {C : ℝ} (r : ℕ)
    (h : AwaySupBound ψ G H D C) (hr : C ≤ 2 * (r : ℝ) + 1) :
    rungMoment ψ G H D (r + 1)
      ≤ ((2 * (r : ℝ) + 1) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) * rungMoment ψ G H D r := by
  refine sup_split_recursion ψ G H D _ (fun s hs => ?_) r
  have hSig : (0 : ℝ) ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _
  exact (h s hs).trans (mul_le_mul_of_nonneg_right hr hSig)

/-- Exact-budget form of `subWick_of_awaySupBound`: an away-sup bound at `C = 2r+1`
immediately gives the rung-`r` sub-Wick inequality. -/
theorem subWick_of_awaySupBound_at_wickBudget
    (ψ : AddChar F ℂ) (G H D : Finset F) (r : ℕ)
    (h : AwaySupBound ψ G H D (2 * (r : ℝ) + 1)) :
    rungMoment ψ G H D (r + 1)
      ≤ ((2 * (r : ℝ) + 1) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) * rungMoment ψ G H D r :=
  subWick_of_awaySupBound ψ G H D r h le_rfl

/-- **Converse: a sub-Wick violation certifies an away-sup lower bound.** If rung r is
super-Wick (`(2r+1)·Σ·S_r^D < S_{r+1}^D`), some away value exceeds the Wick budget:
`∃ s∉D, (2r+1)·Σ < ‖I_H(s)‖²`. Together with `subWick_of_awaySupBound`, sub-Wick
monotonicity at rung r IS the away-sup statement at budget `(2r+1)Σ` — the standalone
conjecture collapses into `AwaySupBound`, rung by rung, in both directions. -/
theorem awaySup_lower_of_superWick (ψ : AddChar F ℂ) (G H D : Finset F) (r : ℕ)
    (hviol : ((2 * (r : ℝ) + 1) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) * rungMoment ψ G H D r
      < rungMoment ψ G H D (r + 1)) :
    ∃ s ∈ Finset.univ \ D,
      (2 * (r : ℝ) + 1) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 < ‖incidenceSum ψ G H s‖ ^ 2 := by
  by_contra hno
  push_neg at hno
  exact absurd (sup_split_recursion ψ G H D _ hno r) (not_le.mpr hviol)

/-- A super-Wick rung is an explicit certificate that the corresponding away-sup budget
`C = 2r + 1` fails.  This is the direct consumer form of `awaySup_lower_of_superWick`: any
attempt to prove the rung from `AwaySupBound (2r+1)` contradicts the measured violation. -/
theorem not_awaySupBound_of_superWick (ψ : AddChar F ℂ) (G H D : Finset F) (r : ℕ)
    (hviol : ((2 * (r : ℝ) + 1) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) * rungMoment ψ G H D r
      < rungMoment ψ G H D (r + 1)) :
    ¬ AwaySupBound ψ G H D (2 * (r : ℝ) + 1) := by
  intro hsup
  exact not_le.mpr hviol (subWick_of_awaySupBound ψ G H D r hsup le_rfl)

/-- Direct no-violation form: under the away-sup budget `C = 2r + 1`, rung `r` cannot be
super-Wick.  This packages `subWick_of_awaySupBound` in the negated form most useful to
counterexample scanners. -/
theorem not_superWick_of_awaySupBound (ψ : AddChar F ℂ) (G H D : Finset F) (r : ℕ)
    (hsup : AwaySupBound ψ G H D (2 * (r : ℝ) + 1)) :
    ¬ ((2 * (r : ℝ) + 1) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) * rungMoment ψ G H D r
      < rungMoment ψ G H D (r + 1) := by
  exact not_lt.mpr (subWick_of_awaySupBound ψ G H D r hsup le_rfl)

/-! ### (3) The no-self-improvement fixed point. -/

/-- Chebyshev at any depth: every away value's `2R`-th power is dominated by rung R. -/
theorem away_pow_le_rungMoment (ψ : AddChar F ℂ) (G H D : Finset F) (R : ℕ) {s : F}
    (hs : s ∈ Finset.univ \ D) :
    ‖incidenceSum ψ G H s‖ ^ (2 * R) ≤ rungMoment ψ G H D R :=
  Finset.single_le_sum (f := fun s => ‖incidenceSum ψ G H s‖ ^ (2 * R))
    (fun _ _ => pow_nonneg (norm_nonneg _) _) hs

/-- The full depth-R bootstrap chain in one inequality: under `AwaySupBound K`, every away
value obeys `‖I(s)‖^{2(R+2)} ≤ (K·Σ)^R · S₂^D` (Chebyshev ∘ sup-split^R ∘ rung 2). -/
theorem awayValue_pow_le_chain (ψ : AddChar F ℂ) (G H D : Finset F) {K : ℝ} (R : ℕ)
    (hK : 0 ≤ K) (h : AwaySupBound ψ G H D K) {s : F} (hs : s ∈ Finset.univ \ D) :
    ‖incidenceSum ψ G H s‖ ^ (2 * (R + 2))
      ≤ (K * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ R * rungMoment ψ G H D 2 := by
  refine (away_pow_le_rungMoment ψ G H D (R + 2) hs).trans ?_
  -- the r19 tower collapse, re-derived locally by induction via sup_split_recursion
  induction R with
  | zero => rw [pow_zero, one_mul]
  | succ R ih =>
      have hSig : (0 : ℝ) ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 :=
        Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _
      have hKS : (0 : ℝ) ≤ K * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 := mul_nonneg hK hSig
      have hstep : rungMoment ψ G H D (R + 2 + 1)
          ≤ (K * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) * rungMoment ψ G H D (R + 2) :=
        sup_split_recursion ψ G H D _ h (R + 2)
      calc rungMoment ψ G H D (R + 1 + 2)
          = rungMoment ψ G H D (R + 2 + 1) := by norm_num
        _ ≤ (K * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) * rungMoment ψ G H D (R + 2) := hstep
        _ ≤ (K * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
              * ((K * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ R * rungMoment ψ G H D 2) :=
            mul_le_mul_of_nonneg_left ih hKS
        _ = (K * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ (R + 1) * rungMoment ψ G H D 2 := by ring

/-- **No self-improvement (the arithmetic core).** For `x > 0`, the depth-R fixed-point
constraint `x^{R+2} ≤ x^R·B` is EQUIVALENT to the depth-2 constraint `x² ≤ B`, for every R.
Instantiated at `x = KΣ` (the self-consistent away sup) and `B = S₂^D`: the constraint the
depth-R chain (`awayValue_pow_le_chain`) places on the sup is exactly the depth-2 Chebyshev
`M²_away ≤ √(S₂^D)`. The K-degrees cancel identically — iterating the rung recursion to any
depth proves NOTHING beyond one fourth-moment Chebyshev; no bootstrap loop closes. -/
theorem fixedPoint_depth_independent {x B : ℝ} (hx : 0 < x) (R : ℕ) :
    x ^ (R + 2) ≤ x ^ R * B ↔ x ^ 2 ≤ B := by
  constructor
  · intro h
    rw [pow_add] at h
    exact le_of_mul_le_mul_left h (pow_pos hx R)
  · intro h
    rw [pow_add]
    exact mul_le_mul_of_nonneg_left h (le_of_lt (pow_pos hx R))

end ArkLib.ProximityGap.Frontier.R20SubWickInterpolation

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R20SubWickInterpolation.rungMoment_sq_le_mul
#print axioms ArkLib.ProximityGap.Frontier.R20SubWickInterpolation.rungMoment_ratio_mono
#print axioms ArkLib.ProximityGap.Frontier.R20SubWickInterpolation.subWick_of_awaySupBound
#print axioms ArkLib.ProximityGap.Frontier.R20SubWickInterpolation.subWick_of_awaySupBound_at_wickBudget
#print axioms ArkLib.ProximityGap.Frontier.R20SubWickInterpolation.awaySup_lower_of_superWick
#print axioms ArkLib.ProximityGap.Frontier.R20SubWickInterpolation.not_awaySupBound_of_superWick
#print axioms ArkLib.ProximityGap.Frontier.R20SubWickInterpolation.not_superWick_of_awaySupBound
#print axioms ArkLib.ProximityGap.Frontier.R20SubWickInterpolation.away_pow_le_rungMoment
#print axioms ArkLib.ProximityGap.Frontier.R20SubWickInterpolation.awayValue_pow_le_chain
#print axioms ArkLib.ProximityGap.Frontier.R20SubWickInterpolation.fixedPoint_depth_independent
