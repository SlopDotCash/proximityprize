/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R21HigherDFaces
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R20StepanovScaffold

/-!
# LANE ORDER2LINK (#466 round 22): the order-2 member of `TripleLinearHasse` IS
# `LegendreCubicHasse` — formalized affine reindex, all edge cases discharged

R21 (`_R21HigherDFaces.lean`) asserted, in prose only, that the order-2 member of the
`TripleLinearHasse` family "is implied by `LegendreCubicHasse` via the R20 normal form".
This file FORMALIZES that link, so that when `CubicStepanovUpper` (R20/R21 Stepanov lane)
lands, the d = 2 member of the R21 family fires automatically.

## The mathematics (probe-exact at p = 13, 29, 53, 97: `probe_r22_order2link.py`, 0 failures)

For the quadratic character `χ` (so `conj χ = χ`), the reduced triple-linear sum is
`T(u,v,w) = ∑_s χ((us+1)(vs+1)(ws+1))`, `u = y₂−x₁`, `v = y₂−x₂`, `w = y₂−y₁`.

* **Main case** (`u,v,w` nonzero, pairwise distinct): the affine reindex `s = t − w⁻¹`
  factors the kernel: `us+1 = u(t−u')`, `vs+1 = v(t−v')`, `ws+1 = wt`, with
  `u' = w⁻¹−u⁻¹`, `v' = w⁻¹−v⁻¹` (nonzero, distinct).  Hence the EXACT identity
  `T = χ(uvw)·∑_t χ(t(t−u')(t−v'))` — a `χ`-of-constant twist times the Legendre cubic —
  and `T² ≤ 4p` from `LegendreCubicHasse`.
* **Edge cases** (coincidences/zeros not excluded by `¬IsDegenerate`):
  - one of `u,v,w` zero, other two distinct nonzero: `T = −χ(ab)` (complete quadratic);
  - two equal nonzero (`u = v ≠ 0`, any `w ≠ 0`, including `w = u`): the square factor
    absorbs, `T = −χ(1 − w/u)` (which is `0` when `w = u`);
  - two zeros: `T = 0` (complete linear sum).
  All have `T² ≤ 1 ≤ 4p`.
* **Excluded cases** = exactly `IsDegenerate` in `(u,v,w)` coordinates: "some two of
  `u,v,w` equal AND the third zero" (probe: there `T ∈ {p−1, p}`, genuinely unbounded —
  the nondegeneracy hypothesis is NECESSARY, not an artifact).

## Proven here (axiom-clean)

* `tripleSumZ_eq_mul_cubic` — the exact affine-reindex identity (main case).
* `tripleSumZ_sq_le` — `T² ≤ 4p` for every nondegenerate `(u,v,w)`, from
  `LegendreCubicHasse` (integer-clean; full edge-case analysis).
* `tripleLinearHasse_of_legendreCubicHasse` — **THE LANE RESULT**: for the complexified
  quadratic character `qchar F`, `LegendreCubicHasse F → TripleLinearHasse (qchar F) G`.
* `tripleLinearHasse_of_stepanovUpper` — chained through R20: `CubicStepanovUpper F B`
  (with `0 ≤ B`, `B² ≤ 4p`) fires the d = 2 member of the R21 family.
* `quarticWeilInput_qchar_of_legendreCubicHasse` — the R18 `QuarticWeilInput` for
  `qchar F` from `LegendreCubicHasse` (via the R21 reduction, `p ≥ 4`).
* `orderTwo_index_set_eq` / `card_orderTwo_index` — the HONEST MASS ACCOUNTING core:
  in `chiFamily χ = {χ^j : 1 ≤ j < m}` with `m = 2^μ`, the index `j` has
  `m / gcd(m,j) = 2` (i.e. `χ^j` of order 2) for EXACTLY ONE `j`, namely `j = 2^{μ−1}`.

## HONEST mass accounting (what the d = 2 discharge actually buys)

`chiFamily χ` has `m − 1` members, all of 2-power order `d | m` (`m = 2^μ` in the prize
regime); the number of order-`2^k` members is `φ(2^k) = 2^{k−1}`.  So:
* order-2 members: **exactly 1 of `m − 1`** (mass `1/(m−1)`; `≈ 9.3×10⁻¹⁰` at `m = 2³⁰`);
* order-`m` members: `m/2` of `m − 1` (mass `≈ 1/2`); order `≥ 2^k`: mass `≈ 2^{1−k}`-tail
  from below, i.e. HALF the family sits at the MAXIMAL order and almost all of it at
  order `≥ m/2^{O(1)}`.
The r = 2 rung (`FourthMomentTwistBound`, uniform weight per character) therefore gets
`1/(m−1)` of its mass from this file's link + the Stepanov push; the BULK of the rung
still rests on the superelliptic (`d ≥ 4`, overwhelmingly `d ∈ {m/2, m}`) members of
`TripleLinearHasse` — genus ≤ d−1 curves, NOT reachable by the genus-1 Stepanov lane.
`K(m)` is untouched.  No closure claimed: `LegendreCubicHasse`, `CubicStepanovUpper`,
and the `d ≥ 4` members of `TripleLinearHasse` all remain named open Props.

Issue #466, round 22, ORDER2LINK lane.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R22Order2Link

open ArkLib.ProximityGap.Frontier.R18FourthMomentTwist
open ArkLib.ProximityGap.Frontier.R19HasseAudit
open ArkLib.ProximityGap.Frontier.R20StepanovScaffold
open ArkLib.ProximityGap.Frontier.R21HigherDFaces

local notation "conj'" => starRingEnd ℂ

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## The integer-valued triple-linear sum (quadratic character) -/

/-- The d = 2 triple-linear sum, integer-valued:
`T(u,v,w) = ∑_s χ((us+1)(vs+1)(ws+1))` for `χ = quadraticChar F`. -/
def tripleSumZ (u v w : F) : ℤ :=
  ∑ s : F, quadraticChar F ((u * s + 1) * ((v * s + 1) * (w * s + 1)))

/-- `T` is symmetric in its first two arguments. -/
theorem tripleSumZ_comm₁ (u v w : F) : tripleSumZ u v w = tripleSumZ v u w :=
  Finset.sum_congr rfl fun s _ => congrArg _ (by ring)

/-- `T` is symmetric in its last two arguments. -/
theorem tripleSumZ_comm₂ (u v w : F) : tripleSumZ u v w = tripleSumZ u w v :=
  Finset.sum_congr rfl fun s _ => congrArg _ (by ring)

/-- Complete linear sum: `∑_s χ(ws+1) = 0` for `w ≠ 0`. -/
theorem sum_quadraticChar_linear (hF : ringChar F ≠ 2) {w : F} (hw : w ≠ 0) :
    ∑ s : F, quadraticChar F (w * s + 1) = 0 := by
  have hbij : Function.Bijective (fun s : F => w * s + 1) := by
    constructor
    · intro a b h
      exact mul_left_cancel₀ hw (by
        have : w * a = w * b := by
          have h' : w * a + 1 = w * b + 1 := h
          linear_combination h'
        exact this)
    · intro t
      refine ⟨w⁻¹ * (t - 1), ?_⟩
      show w * (w⁻¹ * (t - 1)) + 1 = t
      rw [← mul_assoc, mul_inv_cancel₀ hw, one_mul]
      ring
  calc ∑ s : F, quadraticChar F (w * s + 1)
      = ∑ t : F, quadraticChar F t :=
        Fintype.sum_bijective _ hbij _ _ (fun s => rfl)
    _ = 0 := quadraticChar_sum_zero hF

/-- Two distinct linear factors: `∑_s χ((us+1)(vs+1)) = −χ(uv)`. -/
theorem sum_quadraticChar_two_linear (hF : ringChar F ≠ 2) {u v : F}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    ∑ s : F, quadraticChar F ((u * s + 1) * (v * s + 1))
      = -quadraticChar F (u * v) := by
  have key : ∀ s : F, (u * s + 1) * (v * s + 1)
      = (u * v) * ((s - (-u⁻¹)) * (s - (-v⁻¹))) := by
    intro s
    field_simp
    ring
  have hne : (-u⁻¹ : F) ≠ -v⁻¹ := by
    intro h
    exact huv (inv_injective (neg_injective h))
  calc ∑ s : F, quadraticChar F ((u * s + 1) * (v * s + 1))
      = ∑ s : F, quadraticChar F (u * v)
          * quadraticChar F ((s - (-u⁻¹)) * (s - (-v⁻¹))) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [key s, map_mul]
    _ = quadraticChar F (u * v)
          * ∑ s : F, quadraticChar F ((s - (-u⁻¹)) * (s - (-v⁻¹))) := by
        rw [Finset.mul_sum]
    _ = -quadraticChar F (u * v) := by
        rw [sum_quadraticChar_quadratic hF hne]
        ring

/-- Two zero slots: `T(0,0,w) = 0` for `w ≠ 0`. -/
theorem tripleSumZ_two_zero (hF : ringChar F ≠ 2) {w : F} (hw : w ≠ 0) :
    tripleSumZ 0 0 w = 0 := by
  have h : ∀ s : F, ((0 : F) * s + 1) * (((0 : F) * s + 1) * (w * s + 1))
      = w * s + 1 := by intro s; ring
  unfold tripleSumZ
  rw [Finset.sum_congr rfl fun s _ => congrArg _ (h s)]
  exact sum_quadraticChar_linear hF hw

/-- One zero slot: `T(u,v,0) = −χ(uv)` for `u,v` distinct nonzero. -/
theorem tripleSumZ_one_zero (hF : ringChar F ≠ 2) {u v : F}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    tripleSumZ u v 0 = -quadraticChar F (u * v) := by
  have h : ∀ s : F, (u * s + 1) * ((v * s + 1) * ((0 : F) * s + 1))
      = (u * s + 1) * (v * s + 1) := by intro s; ring
  unfold tripleSumZ
  rw [Finset.sum_congr rfl fun s _ => congrArg _ (h s)]
  exact sum_quadraticChar_two_linear hF hu hv huv

/-- Repeated factor (square absorption): `T(u,u,w) = −χ(1 − w·u⁻¹)` for `u,w ≠ 0`
(covers `w = u`: then the value is `−χ(0) = 0`, the all-equal case). -/
theorem tripleSumZ_double (hF : ringChar F ≠ 2) {u w : F} (hu : u ≠ 0) (hw : w ≠ 0) :
    tripleSumZ u u w = -quadraticChar F (1 - w * u⁻¹) := by
  have hkey : ∀ s : F, (u * s + 1) * ((u * s + 1) * (w * s + 1))
      = (u * s + 1) ^ 2 * (w * s + 1) := by intro s; ring
  have hstep : tripleSumZ u u w
      = ∑ s : F, quadraticChar F ((u * s + 1) ^ 2) * quadraticChar F (w * s + 1) := by
    unfold tripleSumZ
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hkey s, map_mul]
  -- split off s₀ = −u⁻¹ (the vanishing point of the square factor)
  have hs₀ : u * (-u⁻¹) + 1 = 0 := by
    rw [mul_neg, mul_inv_cancel₀ hu]
    ring
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun s : F => quadraticChar F ((u * s + 1) ^ 2) * quadraticChar F (w * s + 1))
    (Finset.mem_univ (-u⁻¹ : F))
  have hzero : quadraticChar F ((u * (-u⁻¹) + 1) ^ 2) * quadraticChar F (w * (-u⁻¹) + 1)
      = 0 := by
    rw [hs₀]
    simp
  -- on the erased set the square factor is 1
  have hsq : ∀ s ∈ Finset.univ.erase (-u⁻¹ : F),
      quadraticChar F ((u * s + 1) ^ 2) * quadraticChar F (w * s + 1)
        = quadraticChar F (w * s + 1) := by
    intro s hs
    have hne : u * s + 1 ≠ 0 := by
      intro h
      have hus : u * s = -1 := by linear_combination h
      have : s = -u⁻¹ := by
        have : u⁻¹ * (u * s) = u⁻¹ * (-1) := by rw [hus]
        rwa [← mul_assoc, inv_mul_cancel₀ hu, one_mul, mul_neg, mul_one] at this
      exact (Finset.mem_erase.mp hs).1 this
    rw [quadraticChar_sq_one' hne, one_mul]
  -- the erased linear sum
  have hlin : (∑ s ∈ Finset.univ.erase (-u⁻¹ : F), quadraticChar F (w * s + 1))
      + quadraticChar F (w * (-u⁻¹) + 1) = 0 := by
    have h := Finset.sum_erase_add Finset.univ
      (fun s : F => quadraticChar F (w * s + 1)) (Finset.mem_univ (-u⁻¹ : F))
    rw [sum_quadraticChar_linear hF hw] at h
    exact h
  have harg : w * (-u⁻¹) + 1 = 1 - w * u⁻¹ := by ring
  rw [harg] at hlin
  calc tripleSumZ u u w
      = ∑ s : F, quadraticChar F ((u * s + 1) ^ 2) * quadraticChar F (w * s + 1) := hstep
    _ = (∑ s ∈ Finset.univ.erase (-u⁻¹ : F),
          quadraticChar F ((u * s + 1) ^ 2) * quadraticChar F (w * s + 1))
        + quadraticChar F ((u * (-u⁻¹) + 1) ^ 2) * quadraticChar F (w * (-u⁻¹) + 1) :=
        hsplit.symm
    _ = ∑ s ∈ Finset.univ.erase (-u⁻¹ : F), quadraticChar F (w * s + 1) := by
        rw [hzero, add_zero]
        exact Finset.sum_congr rfl hsq
    _ = -quadraticChar F (1 - w * u⁻¹) := by linarith

/-- **The exact affine-reindex identity (main case)**: for `u, v, w` nonzero and pairwise
distinct, the reindex `s = t − w⁻¹` gives
`T(u,v,w) = χ(uvw) · ∑_t χ(t(t−u')(t−v'))`, `u' = w⁻¹−u⁻¹`, `v' = w⁻¹−v⁻¹` —
the triple-linear sum is a `χ`-of-constant twist of the Legendre cubic sum. -/
theorem tripleSumZ_eq_mul_cubic {u v w : F} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    tripleSumZ u v w
      = quadraticChar F (u * v * w)
        * ∑ t : F, quadraticChar F
            (t * ((t - (w⁻¹ - u⁻¹)) * (t - (w⁻¹ - v⁻¹)))) := by
  have hbij : Function.Bijective (fun t : F => t - w⁻¹) :=
    (Equiv.subRight (w⁻¹ : F)).bijective
  have hpoint : ∀ t : F,
      quadraticChar F (u * v * w)
          * quadraticChar F (t * ((t - (w⁻¹ - u⁻¹)) * (t - (w⁻¹ - v⁻¹))))
        = quadraticChar F
            ((u * (t - w⁻¹) + 1) * ((v * (t - w⁻¹) + 1) * (w * (t - w⁻¹) + 1))) := by
    intro t
    rw [← map_mul]
    congr 1
    field_simp
    ring
  have hre : ∑ t : F, quadraticChar F (u * v * w)
        * quadraticChar F (t * ((t - (w⁻¹ - u⁻¹)) * (t - (w⁻¹ - v⁻¹))))
      = ∑ s : F, quadraticChar F ((u * s + 1) * ((v * s + 1) * (w * s + 1))) :=
    Fintype.sum_bijective _ hbij _ _ (fun t => hpoint t)
  unfold tripleSumZ
  rw [← hre, Finset.mul_sum]

/-! ## The master bound -/

/-- **`T² ≤ 4p` for every nondegenerate `(u,v,w)`** (integer-clean), given
`LegendreCubicHasse`.  The three excluded clauses are EXACTLY `IsDegenerate` in
`(u,v,w) = (y₂−x₁, y₂−x₂, y₂−y₁)` coordinates; on them `T ∈ {p−1, p}` (probe), so the
hypothesis is necessary. -/
theorem tripleSumZ_sq_le (hF : ringChar F ≠ 2)
    (hH : LegendreCubicHasse F) (u v w : F)
    (h1 : ¬(u = v ∧ w = 0)) (h2 : ¬(u = w ∧ v = 0)) (h3 : ¬(v = w ∧ u = 0)) :
    (tripleSumZ u v w) ^ 2 ≤ 4 * (Fintype.card F : ℤ) := by
  have hc : (0 : ℤ) < (Fintype.card F : ℤ) := by exact_mod_cast Fintype.card_pos
  have hp1 : (1 : ℤ) ≤ 4 * (Fintype.card F : ℤ) := by omega
  have hchi_sq : ∀ a : F, (quadraticChar F a) ^ 2 ≤ 1 := by
    intro a
    rcases (quadraticChar_isQuadratic F) a with h | h | h <;> rw [h] <;> norm_num
  have hneg_sq : ∀ a : F, (-quadraticChar F a) ^ 2 ≤ 4 * (Fintype.card F : ℤ) := by
    intro a
    rw [neg_sq]
    exact le_trans (hchi_sq a) hp1
  by_cases hu0 : u = 0
  · subst hu0
    by_cases hv0 : v = 0
    · subst hv0
      have hw0 : w ≠ 0 := fun h => h1 ⟨rfl, h⟩
      rw [tripleSumZ_two_zero hF hw0]
      nlinarith [hc]
    · by_cases hw0 : w = 0
      · subst hw0
        rw [tripleSumZ_comm₂, tripleSumZ_two_zero hF hv0]
        nlinarith [hc]
      · have hvw : v ≠ w := fun h => h3 ⟨h, rfl⟩
        rw [tripleSumZ_comm₁, tripleSumZ_comm₂, tripleSumZ_one_zero hF hv0 hw0 hvw]
        exact hneg_sq _
  · by_cases hv0 : v = 0
    · subst hv0
      by_cases hw0 : w = 0
      · subst hw0
        rw [tripleSumZ_comm₁, tripleSumZ_comm₂, tripleSumZ_two_zero hF hu0]
        nlinarith [hc]
      · have huw : u ≠ w := fun h => h2 ⟨h, rfl⟩
        rw [tripleSumZ_comm₂, tripleSumZ_one_zero hF hu0 hw0 huw]
        exact hneg_sq _
    · by_cases hw0 : w = 0
      · subst hw0
        have huv : u ≠ v := fun h => h1 ⟨h, rfl⟩
        rw [tripleSumZ_one_zero hF hu0 hv0 huv]
        exact hneg_sq _
      · -- all nonzero
        by_cases huv : u = v
        · subst huv
          rw [tripleSumZ_double hF hu0 hw0]
          exact hneg_sq _
        · by_cases huw : u = w
          · subst huw
            rw [tripleSumZ_comm₂, tripleSumZ_double hF hu0 hv0]
            exact hneg_sq _
          · by_cases hvw : v = w
            · subst hvw
              rw [tripleSumZ_comm₁, tripleSumZ_comm₂, tripleSumZ_double hF hv0 hu0]
              exact hneg_sq _
            · -- main case: pairwise distinct nonzero
              have hu' : (w⁻¹ - u⁻¹ : F) ≠ 0 := by
                intro h
                exact huw (inv_injective (sub_eq_zero.mp h)).symm
              have hv' : (w⁻¹ - v⁻¹ : F) ≠ 0 := by
                intro h
                exact hvw (inv_injective (sub_eq_zero.mp h)).symm
              have hne : (w⁻¹ - u⁻¹ : F) ≠ w⁻¹ - v⁻¹ := by
                intro h
                exact huv (inv_injective (by
                  have := sub_right_inj.mp h
                  exact this))
              rw [tripleSumZ_eq_mul_cubic hu0 hv0 hw0, mul_pow,
                quadraticChar_sq_one (mul_ne_zero (mul_ne_zero hu0 hv0) hw0), one_mul]
              exact hH _ _ hu' hv' hne

/-! ## The complex bridge: the complexified quadratic character -/

/-- The complexified quadratic character — the UNIQUE order-2 member shape of the
R19/R21 chi-family (over ℂ). -/
noncomputable def qchar (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

theorem qchar_apply (x : F) : qchar F x = ((quadraticChar F x : ℤ) : ℂ) := rfl

/-- `qchar` is conjugation-fixed (real-valued): `conj (qchar x) = qchar x`. -/
theorem conj_qchar (x : F) : conj' (qchar F x) = qchar F x := by
  rw [qchar_apply]
  exact map_intCast (starRingEnd ℂ) _

/-- The complex triple-linear sum of `qchar` IS the integer sum, cast. -/
theorem tripleSum_qchar (u v w : F) :
    tripleSum (qchar F) u v w = ((tripleSumZ u v w : ℤ) : ℂ) := by
  unfold tripleSum tripleSumZ
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [conj_qchar, ← map_mul, qchar_apply, mul_assoc]

/-- Norm transfer: `S² ≤ 4p` (in ℤ) gives `‖(S : ℂ)‖ ≤ 2√p`. -/
theorem norm_intCast_le_two_sqrt {S : ℤ} (h : S ^ 2 ≤ 4 * (Fintype.card F : ℤ)) :
    ‖((S : ℤ) : ℂ)‖ ≤ 2 * Real.sqrt (Fintype.card F) := by
  have hcast : ((S : ℤ) : ℂ) = (((S : ℤ) : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  have h' : ((S : ℤ) : ℝ) ^ 2 ≤ 4 * (Fintype.card F : ℝ) := by exact_mod_cast h
  have habs : |((S : ℤ) : ℝ)| = Real.sqrt (((S : ℤ) : ℝ) ^ 2) :=
    (Real.sqrt_sq_eq_abs _).symm
  rw [habs]
  calc Real.sqrt (((S : ℤ) : ℝ) ^ 2)
      ≤ Real.sqrt (4 * (Fintype.card F : ℝ)) := Real.sqrt_le_sqrt h'
    _ = 2 * Real.sqrt (Fintype.card F) := by
        rw [show (4 : ℝ) * (Fintype.card F : ℝ)
            = 2 ^ 2 * (Fintype.card F : ℝ) by norm_num,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]

/-! ## THE LANE RESULT -/

/-- **ORDER2LINK**: `LegendreCubicHasse F` implies the order-2 (`qchar`) member of the
R21 `TripleLinearHasse` family, for every evaluation set `G`.  The `¬IsDegenerate`
hypothesis translates EXACTLY to the three excluded `(u,v,w)` clauses. -/
theorem tripleLinearHasse_of_legendreCubicHasse (hF : ringChar F ≠ 2)
    (hH : LegendreCubicHasse F) (G : Finset F) :
    TripleLinearHasse (qchar F) G := by
  intro z hz hnd
  obtain ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩ := z
  have h1 : ¬(y₂ - x₁ = y₂ - x₂ ∧ y₂ - y₁ = 0) := by
    rintro ⟨ha, hb⟩
    exact hnd (Or.inr (Or.inr ⟨sub_right_inj.mp ha, (sub_eq_zero.mp hb).symm⟩))
  have h2 : ¬(y₂ - x₁ = y₂ - y₁ ∧ y₂ - x₂ = 0) := by
    rintro ⟨ha, hb⟩
    exact hnd (Or.inl ⟨sub_right_inj.mp ha, (sub_eq_zero.mp hb).symm⟩)
  have h3 : ¬(y₂ - x₂ = y₂ - y₁ ∧ y₂ - x₁ = 0) := by
    rintro ⟨ha, hb⟩
    exact hnd (Or.inr (Or.inl ⟨(sub_eq_zero.mp hb).symm, sub_right_inj.mp ha⟩))
  have hsq := tripleSumZ_sq_le hF hH (y₂ - x₁) (y₂ - x₂) (y₂ - y₁) h1 h2 h3
  rw [tripleSum_qchar]
  exact norm_intCast_le_two_sqrt hsq

/-- Chained through R20: a one-sided Stepanov bound `CubicStepanovUpper F B`
(`0 ≤ B`, `B² ≤ 4p`) fires the d = 2 member of the R21 family. -/
theorem tripleLinearHasse_of_stepanovUpper (hF : ringChar F ≠ 2) {B : ℤ}
    (hB0 : 0 ≤ B) (hB : B ^ 2 ≤ 4 * Fintype.card F)
    (hU : CubicStepanovUpper F B) (G : Finset F) :
    TripleLinearHasse (qchar F) G :=
  tripleLinearHasse_of_legendreCubicHasse hF
    (legendreCubicHasse_of_stepanovUpper hF hB0 hB hU) G

/-- The R18 `QuarticWeilInput` for the complexified quadratic character, from
`LegendreCubicHasse` (via the R21 reduction; needs `p ≥ 4`). -/
theorem quarticWeilInput_qchar_of_legendreCubicHasse (hF : ringChar F ≠ 2)
    (hH : LegendreCubicHasse F) (G : Finset F)
    (hp4 : (4 : ℝ) ≤ (Fintype.card F : ℝ)) :
    QuarticWeilInput (qchar F) G :=
  quarticWeilInput_of_tripleLinearHasse (qchar F) G hp4
    (tripleLinearHasse_of_legendreCubicHasse hF hH G)

/-! ## The honest mass accounting core (pure ℕ arithmetic)

In `chiFamily χ = {χ^j : 1 ≤ j < m}` with `m = orderOf χ = 2^μ`, the order of `χ^j` is
`m / gcd(m, j)`.  The order-2 members correspond to `m / gcd(m,j) = 2`; the next two
lemmas pin that index set to the SINGLETON `{2^{μ−1}}` — the d = 2 discharge covers
exactly `1` of the `m − 1` family members. -/

/-- The order-2 index set of the 2-power family is the singleton `{2^{μ−1}}`. -/
theorem orderTwo_index_set_eq (μ : ℕ) (hμ : 1 ≤ μ) :
    ((Finset.range (2 ^ μ)).erase 0).filter
        (fun j => 2 ^ μ / Nat.gcd (2 ^ μ) j = 2)
      = {2 ^ (μ - 1)} := by
  have hpow : 2 ^ μ = 2 * 2 ^ (μ - 1) := by
    conv_lhs => rw [show μ = (μ - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hpos : 0 < 2 ^ (μ - 1) := pow_pos (by norm_num) _
  ext j
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hj0, hjm⟩, hq⟩
    have hgpos : 0 < Nat.gcd (2 ^ μ) j :=
      Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hj0)
    obtain ⟨c, hc⟩ := Nat.gcd_dvd_left (2 ^ μ) j
    have hc2 : c = 2 := by
      have h2 : Nat.gcd (2 ^ μ) j * c / Nat.gcd (2 ^ μ) j = 2 := by
        rw [← hc]
        exact hq
      rwa [Nat.mul_div_cancel_left c hgpos] at h2
    have hg : Nat.gcd (2 ^ μ) j = 2 ^ (μ - 1) := by
      rw [hc2] at hc
      omega
    have hdvd : 2 ^ (μ - 1) ∣ j := hg ▸ Nat.gcd_dvd_right (2 ^ μ) j
    obtain ⟨k, hk⟩ := hdvd
    have hk0 : k ≠ 0 := fun h => hj0 (by simp [hk, h])
    have hklt : k < 2 := by
      by_contra hge
      push_neg at hge
      have hmul : 2 ^ (μ - 1) * 2 ≤ 2 ^ (μ - 1) * k :=
        Nat.mul_le_mul_left _ hge
      rw [← hk] at hmul
      omega
    have hk1 : k = 1 := by omega
    rw [hk, hk1, mul_one]
  · rintro rfl
    refine ⟨⟨hpos.ne', by omega⟩, ?_⟩
    have hg : Nat.gcd (2 ^ μ) (2 ^ (μ - 1)) = 2 ^ (μ - 1) := by
      rw [Nat.gcd_comm]
      exact Nat.gcd_eq_left (pow_dvd_pow 2 (by omega))
    rw [hg, hpow]
    exact Nat.mul_div_cancel _ hpos

/-- **The mass count**: exactly ONE of the `2^μ − 1` family indices has order 2 —
the d = 2 discharge covers `1/(m−1)` of the r = 2 rung's character mass. -/
theorem card_orderTwo_index (μ : ℕ) (hμ : 1 ≤ μ) :
    (((Finset.range (2 ^ μ)).erase 0).filter
        (fun j => 2 ^ μ / Nat.gcd (2 ^ μ) j = 2)).card = 1 := by
  rw [orderTwo_index_set_eq μ hμ]
  rfl

end ArkLib.ProximityGap.Frontier.R22Order2Link

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R22Order2Link.tripleSumZ_eq_mul_cubic
#print axioms ArkLib.ProximityGap.Frontier.R22Order2Link.tripleSumZ_sq_le
#print axioms
  ArkLib.ProximityGap.Frontier.R22Order2Link.tripleLinearHasse_of_legendreCubicHasse
#print axioms ArkLib.ProximityGap.Frontier.R22Order2Link.tripleLinearHasse_of_stepanovUpper
#print axioms
  ArkLib.ProximityGap.Frontier.R22Order2Link.quarticWeilInput_qchar_of_legendreCubicHasse
#print axioms ArkLib.ProximityGap.Frontier.R22Order2Link.orderTwo_index_set_eq
#print axioms ArkLib.ProximityGap.Frontier.R22Order2Link.card_orderTwo_index
