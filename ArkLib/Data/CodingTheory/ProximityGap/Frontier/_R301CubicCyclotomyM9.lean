/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R300DistStratumAccounting

/-!
# LANE B2 (#466, r=3 rung, m = 9): the smallest open DIST instance DISCHARGES
  unconditionally — support collapse on `{0,3,6}` plus counting; the cubic-cyclotomy
  closed-form candidates are REFUTED with mechanism

## Probe verdicts (`scripts/probes/probe_466_r3_m9_cubic_cyclotomy.py`, exact,
   32 primes `p ≡ 1 (mod 9)` up to 1171)

* **Support collapse (CONFIRMED, formalized below)**: at `m = 9` (`u = 3`) there are
  exactly three `H`-cosets, so a DIST triple carries label multiset `{0,1,2}` whose
  sum is `0 mod 3` — `distStratum(d) = 0` off `d ∈ {0, 3, 6}`, and the bad-index
  count is `≤ 6` per `(d,j)` (kernel-checked by `decide`).  Counting then closes the
  rung: `DistStratumEnergyBound J 3 q 10` for EVERY `J` with `‖J‖² ≤ q` —
  measured sharp constant over the probed primes: `C_D(9) = 1.87` (so `10` has
  ≥ 5× headroom; the bound is unconditional, no cancellation used).
* **Refutation 1 (generator dependence)**: the per-character energy `E_DIST` is NOT
  a function of `p` alone — switching the primitive root changes it by ~25% at
  `p = 109`.  Mechanism: fixing `χ = λ` picks one Galois conjugate among the six
  order-9 characters, and `E_DIST` is not Galois-invariant.  Hence NO closed form
  in the cubic cyclotomic numbers `(L, M)` (`4p = L² + 27M²`) exists for fixed χ.
* **Structure (numeric)**: the Galois-AVERAGED energy over the six order-9
  characters is an EXACT INTEGER at every probed prime (distance to ℤ `< 10⁻⁴`
  at magnitude `10¹¹`) — as predicted by Galois invariance + algebraic
  integrality.  Not formalized (needs algebraic-number-theoretic machinery with
  no in-tree counterpart); recorded as probe-only structure.
* **Refutation 2 ((L,M)-basis)**: even the Galois-averaged integer energy admits
  NO exact linear closed form on the monomial basis
  `{p³, p², p²L, pL², pM², p, 1}` (least-squares residual `4×10²`, i.e. total
  failure).  Mechanism: the DIST energy lives in NONIC (order-9) cyclotomy —
  the degree-6 field `ℚ(ζ₉)` — and is not determined by the cubic subfield data
  `(L, M)`.  Any exact evaluation must use the `ℤ[ζ₉]` prime decomposition of
  `p`, not Gauss's cubic invariants.

## What this brick lands (all axiom-clean; `decide`-kernel-checked finite parts)

* `m9_dist_support` — the label-sum obstruction: a DIST triple at `m = 9` forces
  `d ∈ {0, 3, 6}`;
* `distStratum_m9_eq_zero` — `distStratum J 3 d = 0` off the support;
* `m9_inner_card_le` — the per-`(d,j)` DIST index count is `≤ 6`;
* `norm_distStratum_m9_le` — `‖distStratum J 3 d‖ ≤ 48·B³`;
* **`distStratumEnergyBound_rung_m9`** — the m = 9 rung DISCHARGED:
  `DistStratumEnergyBound J 3 q 10` unconditionally (`3·(48)² = 6912 ≤ 10·729`).

With the R300 rungs `m = 3, 6` (`C = 0`) and this brick, the first m with open
DIST content is `m = 12` (`u = 4`: four cosets, no support collapse, counts
`Θ(m²)` per output — genuinely analytic).  The lane rests here.  CORE OPEN,
ON-BGK.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R301CubicCyclotomyM9

open ArkLib.ProximityGap.Frontier.R300DistStratumAccounting

/-- **The label-sum obstruction at m = 9**: all-distinct coset labels forces the
output index into `{0, 3, 6}` (kernel-checked over all 729 cases). -/
theorem m9_dist_support :
    ∀ d j i : ZMod 9, allCosetsDistinct (3 : ZMod 9) i (d - j - i) j →
      (d = 0 ∨ d = 3 ∨ d = 6) := by decide

/-- The DIST stratum at m = 9 vanishes off the support `{0, 3, 6}`. -/
theorem distStratum_m9_eq_zero (J : ZMod 9 → ℂ) {d : ZMod 9}
    (hd : ¬(d = 0 ∨ d = 3 ∨ d = 6)) :
    distStratum J 3 d = 0 := by
  unfold distStratum
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [Finset.filter_false_of_mem, Finset.sum_empty]
  intro i _ hpred
  exact hd (m9_dist_support d j i hpred)

/-- The per-`(d, j)` DIST index set at m = 9 has at most 6 elements
(kernel-checked over all 81 cases). -/
theorem m9_inner_card_le :
    ∀ d j : ZMod 9,
      (((Finset.univ \ {(0 : ZMod 9)}).filter (fun i => d - j - i ≠ 0)).filter
          (fun i => allCosetsDistinct (3 : ZMod 9) i (d - j - i) j)).card ≤ 6 := by
  decide

/-- The outer index set at m = 9 has 8 elements. -/
theorem m9_outer_card :
    ((Finset.univ \ {(0 : ZMod 9)}) : Finset (ZMod 9)).card = 8 := by decide

/-- **Pointwise envelope at m = 9**: `‖distStratum(d)‖ ≤ 48·B³`. -/
theorem norm_distStratum_m9_le {J : ZMod 9 → ℂ} {B : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ i : ZMod 9, ‖J i‖ ≤ B) (d : ZMod 9) :
    ‖distStratum J 3 d‖ ≤ 48 * B ^ 3 := by
  unfold distStratum
  calc ‖∑ j ∈ Finset.univ \ {(0 : ZMod 9)}, ∑ i ∈ _, J i * J (d - j - i) * J j‖
      ≤ ∑ j ∈ Finset.univ \ {(0 : ZMod 9)},
          ‖∑ i ∈ ((Finset.univ \ {(0 : ZMod 9)}).filter (fun i => d - j - i ≠ 0)).filter
              (fun i => allCosetsDistinct (3 : ZMod 9) i (d - j - i) j),
            J i * J (d - j - i) * J j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.univ \ {(0 : ZMod 9)}, ((6 : ℕ) : ℝ) * B ^ 3 := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        exact norm_triple_sum_le hB0 hJ _ (m9_inner_card_le d j) j d
    _ = (((Finset.univ \ {(0 : ZMod 9)}) : Finset (ZMod 9)).card : ℝ)
        * (((6 : ℕ) : ℝ) * B ^ 3) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = 48 * B ^ 3 := by
        rw [m9_outer_card]
        push_cast
        ring

/-- The support has exactly three points. -/
theorem m9_support_card :
    ((Finset.univ : Finset (ZMod 9)).filter
        (fun d => d = 0 ∨ d = 3 ∨ d = 6)).card = 3 := by decide

/-- **THE m = 9 RUNG, DISCHARGED UNCONDITIONALLY**: for every coefficient sequence
with the classical envelope `‖J‖² ≤ q`, `DistStratumEnergyBound J 3 q 10` — no
cancellation, no named inputs: support collapse (3 points) × counting (≤ 48·B³).
Probe-measured sharp constant: `C_D(9) ≈ 1.87`, so the counting constant `10` has
≥ 5× headroom.  Together with R300's `m = 3, 6` rungs (`C = 0`), the first m with
genuinely open DIST content is `m = 12`. -/
theorem distStratumEnergyBound_rung_m9 {J : ZMod 9 → ℂ} {q : ℕ}
    (hJ : ∀ i : ZMod 9, ‖J i‖ ^ 2 ≤ (q : ℝ)) :
    DistStratumEnergyBound J 3 q 10 := by
  unfold DistStratumEnergyBound
  have hB0 : (0 : ℝ) ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  have hJroot : ∀ i : ZMod 9, ‖J i‖ ≤ Real.sqrt (q : ℝ) := by
    intro i
    have h := Real.sqrt_le_sqrt (hJ i)
    rwa [Real.sqrt_sq (norm_nonneg _)] at h
  have hsqrt : (Real.sqrt (q : ℝ)) ^ 6 = (q : ℝ) ^ 3 := by
    have hq0 : 0 ≤ (q : ℝ) := by positivity
    have hs2 : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) := Real.sq_sqrt hq0
    calc (Real.sqrt (q : ℝ)) ^ 6 = ((Real.sqrt (q : ℝ)) ^ 2) ^ 3 := by ring
      _ = (q : ℝ) ^ 3 := by rw [hs2]
  set B : ℝ := Real.sqrt (q : ℝ) with hB
  have hpt : ∀ d : ZMod 9, ‖distStratum J 3 d‖ ^ 2
      ≤ (if d = 0 ∨ d = 3 ∨ d = 6 then (48 * B ^ 3) ^ 2 else 0) := by
    intro d
    by_cases hd : d = 0 ∨ d = 3 ∨ d = 6
    · rw [if_pos hd]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_distStratum_m9_le hB0 hJroot d) 2
    · rw [if_neg hd, distStratum_m9_eq_zero J hd, norm_zero]
      norm_num
  calc ∑ d : ZMod 9, ‖distStratum J 3 d‖ ^ 2
      ≤ ∑ d : ZMod 9, (if d = 0 ∨ d = 3 ∨ d = 6 then (48 * B ^ 3) ^ 2 else 0) :=
        Finset.sum_le_sum (fun d _ => hpt d)
    _ = ∑ _d ∈ (Finset.univ : Finset (ZMod 9)).filter
          (fun d => d = 0 ∨ d = 3 ∨ d = 6), (48 * B ^ 3) ^ 2 :=
        (Finset.sum_filter _ _).symm
    _ = 3 * (48 * B ^ 3) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, m9_support_card]
        norm_num
    _ = 6912 * B ^ 6 := by ring
    _ = 6912 * (q : ℝ) ^ 3 := by rw [hB, hsqrt]
    _ ≤ 10 * ((9 : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 3 := by
        have hq3 : (0 : ℝ) ≤ (q : ℝ) ^ 3 := by positivity
        push_cast
        nlinarith

end ArkLib.ProximityGap.Frontier.R301CubicCyclotomyM9

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.R301CubicCyclotomyM9 in
#print axioms m9_dist_support
open ArkLib.ProximityGap.Frontier.R301CubicCyclotomyM9 in
#print axioms distStratum_m9_eq_zero
open ArkLib.ProximityGap.Frontier.R301CubicCyclotomyM9 in
#print axioms m9_inner_card_le
open ArkLib.ProximityGap.Frontier.R301CubicCyclotomyM9 in
#print axioms norm_distStratum_m9_le
open ArkLib.ProximityGap.Frontier.R301CubicCyclotomyM9 in
#print axioms distStratumEnergyBound_rung_m9
