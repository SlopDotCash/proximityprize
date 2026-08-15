/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# LANE G80K (#466, 2026-07-10): the DIVISOR FIRST MOMENT — exact hyperbola identity
  `Σ_{y ≤ M} d(y) = Σ_{a ≤ M} ⌊M/a⌋` and the dyadic harmonic bound
  `Σ_{a ≤ M} ⌊M/a⌋ ≤ M·(log₂M + 1)` (axiom-clean pure Nat).

## Position

Stepping stone to the divisor SECOND moment (KB §6 target) that upgrades G80L's energy
consumer to the full CG interval bound. This lane lands the first moment completely:

* `sum_card_divisors_eq` : `Σ_{y ∈ [1,M]} d(y) = Σ_{a ∈ [1,M]} M/a` — the exact
  divisor/hyperbola double count (each `a` divides exactly `⌊M/a⌋` integers in `[1, M]`).
* `sum_div_le_dyadic` : `Σ_{a ∈ [1,M]} M/a ≤ M·(Nat.log 2 M + 1)` — dyadic blocks
  `[2^j, 2^{j+1})` each contribute `≤ M`; there are `≤ log₂M + 1` blocks.
* `sum_card_divisors_le` : `Σ_{y ∈ [1,M]} d(y) ≤ M·(Nat.log 2 M + 1)` — the classical
  average-divisor bound `d̄ = O(log M)`, machine-checked in Nat with no analysis.

Pure Nat; no subgroup content. CORE remains OPEN / ON-BGK.

Issue #466. Axiom-clean.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.G80KDivisorFirstMoment

/-- Each `a ≥ 1` divides exactly `M/a` integers in `[1, M]`. -/
theorem card_dvd_Icc (M a : ℕ) :
    ((Finset.Icc 1 M).filter (fun y => a ∣ y)).card = M / a := by
  have h := Nat.card_multiples M a
  have hbij : ((Finset.Icc 1 M).filter (fun y => a ∣ y)).card
      = ((Finset.range M).filter (fun e => a ∣ e + 1)).card := by
    refine Finset.card_nbij' (fun y => y - 1) (fun e => e + 1) ?_ ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      obtain ⟨⟨h1, h2⟩, hdvd⟩ := hy
      constructor
      · omega
      · rwa [Nat.sub_add_cancel h1]
    · intro e he
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at he
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, he.2⟩
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hy
      show y - 1 + 1 = y
      omega
    · intro e _
      show e + 1 - 1 = e
      omega
  rw [hbij, h]

/-- **Exact hyperbola identity**: `Σ_{y ∈ [1,M]} d(y) = Σ_{a ∈ [1,M]} M/a`. -/
theorem sum_card_divisors_eq (M : ℕ) :
    ∑ y ∈ Finset.Icc 1 M, y.divisors.card = ∑ a ∈ Finset.Icc 1 M, M / a := by
  classical
  have hdiv : ∀ y ∈ Finset.Icc 1 M, y.divisors.card
      = ((Finset.Icc 1 M).filter (fun a => a ∣ y)).card := by
    intro y hy
    rw [Finset.mem_Icc] at hy
    congr 1
    ext a
    rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdvd, hy0⟩
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact hy0 (Nat.eq_zero_of_zero_dvd hdvd)
      have haM : a ≤ M := le_trans (Nat.le_of_dvd (by omega) hdvd) hy.2
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr ha0, haM⟩, hdvd⟩
    · rintro ⟨⟨ha1, _⟩, hdvd⟩
      exact ⟨hdvd, by omega⟩
  calc ∑ y ∈ Finset.Icc 1 M, y.divisors.card
      = ∑ y ∈ Finset.Icc 1 M, ((Finset.Icc 1 M).filter (fun a => a ∣ y)).card :=
        Finset.sum_congr rfl hdiv
    _ = ∑ y ∈ Finset.Icc 1 M, ∑ a ∈ Finset.Icc 1 M, (if a ∣ y then 1 else 0) :=
        Finset.sum_congr rfl fun y _ => Finset.card_filter _ _
    _ = ∑ a ∈ Finset.Icc 1 M, ∑ y ∈ Finset.Icc 1 M, (if a ∣ y then 1 else 0) :=
        Finset.sum_comm
    _ = ∑ a ∈ Finset.Icc 1 M, ((Finset.Icc 1 M).filter (fun y => a ∣ y)).card :=
        Finset.sum_congr rfl fun a _ => (Finset.card_filter _ _).symm
    _ = ∑ a ∈ Finset.Icc 1 M, M / a :=
        Finset.sum_congr rfl fun a _ => card_dvd_Icc M a

/-- **Dyadic harmonic bound**: `Σ_{a ∈ [1,M]} M/a ≤ M·(log₂M + 1)`. Each dyadic block
`[2^j, 2^{j+1})` contributes at most `2^j · (M/2^j) ≤ M`; blocks are indexed by
`j = log₂ a ≤ log₂ M`. -/
theorem sum_div_le_dyadic (M : ℕ) :
    ∑ a ∈ Finset.Icc 1 M, M / a ≤ M * (Nat.log 2 M + 1) := by
  classical
  -- bound each term by M / 2^(log₂ a) and group by j = log₂ a
  have hterm : ∀ a ∈ Finset.Icc 1 M, M / a ≤ M / 2 ^ (Nat.log 2 a) := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    exact Nat.div_le_div_left (Nat.pow_log_le_self 2 (by omega)) (by positivity)
  calc ∑ a ∈ Finset.Icc 1 M, M / a
      ≤ ∑ a ∈ Finset.Icc 1 M, M / 2 ^ (Nat.log 2 a) := Finset.sum_le_sum hterm
    _ = ∑ j ∈ Finset.range (Nat.log 2 M + 1),
          ∑ a ∈ (Finset.Icc 1 M).filter (fun a => Nat.log 2 a = j),
            M / 2 ^ (Nat.log 2 a) := by
        have hmaps : ∀ a ∈ Finset.Icc 1 M,
            Nat.log 2 a ∈ Finset.range (Nat.log 2 M + 1) := by
          intro a ha
          rw [Finset.mem_Icc] at ha
          rw [Finset.mem_range]
          have := Nat.log_mono_right (b := 2) ha.2
          omega
        exact (Finset.sum_fiberwise_of_maps_to hmaps
          (fun a => M / 2 ^ (Nat.log 2 a))).symm
    _ ≤ ∑ j ∈ Finset.range (Nat.log 2 M + 1), M := by
        refine Finset.sum_le_sum fun j _ => ?_
        -- block j: each term = M / 2^j; block size ≤ 2^j
        have hsize : ((Finset.Icc 1 M).filter (fun a => Nat.log 2 a = j)).card ≤ 2 ^ j := by
          have hsub : (Finset.Icc 1 M).filter (fun a => Nat.log 2 a = j)
              ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1)) := by
            intro a ha
            rw [Finset.mem_filter, Finset.mem_Icc] at ha
            obtain ⟨⟨h1, _⟩, hlog⟩ := ha
            rw [Finset.mem_Ico]
            constructor
            · rw [← hlog]
              exact Nat.pow_log_le_self 2 (by omega)
            · rw [← hlog]
              exact Nat.lt_pow_succ_log_self (by omega) a
          calc ((Finset.Icc 1 M).filter (fun a => Nat.log 2 a = j)).card
              ≤ (Finset.Ico (2 ^ j) (2 ^ (j + 1))).card := Finset.card_le_card hsub
            _ = 2 ^ (j + 1) - 2 ^ j := Nat.card_Ico _ _
            _ = 2 ^ j := by rw [pow_succ]; omega
        calc ∑ a ∈ (Finset.Icc 1 M).filter (fun a => Nat.log 2 a = j),
              M / 2 ^ (Nat.log 2 a)
            = ∑ a ∈ (Finset.Icc 1 M).filter (fun a => Nat.log 2 a = j), M / 2 ^ j := by
              refine Finset.sum_congr rfl fun a ha => ?_
              rw [(Finset.mem_filter.mp ha).2]
          _ = ((Finset.Icc 1 M).filter (fun a => Nat.log 2 a = j)).card * (M / 2 ^ j) := by
              rw [Finset.sum_const, smul_eq_mul]
          _ ≤ 2 ^ j * (M / 2 ^ j) := Nat.mul_le_mul_right _ hsize
          _ = (M / 2 ^ j) * 2 ^ j := mul_comm _ _
          _ ≤ M := Nat.div_mul_le_self M (2 ^ j)
    _ = M * (Nat.log 2 M + 1) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]

/-- **The classical average-divisor bound**: `Σ_{y ≤ M} d(y) ≤ M·(log₂M + 1)`. -/
theorem sum_card_divisors_le (M : ℕ) :
    ∑ y ∈ Finset.Icc 1 M, y.divisors.card ≤ M * (Nat.log 2 M + 1) :=
  (sum_card_divisors_eq M) ▸ sum_div_le_dyadic M

end ArkLib.ProximityGap.Frontier.G80KDivisorFirstMoment

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G80KDivisorFirstMoment.sum_card_divisors_eq
#print axioms
  ArkLib.ProximityGap.Frontier.G80KDivisorFirstMoment.sum_div_le_dyadic
#print axioms
  ArkLib.ProximityGap.Frontier.G80KDivisorFirstMoment.sum_card_divisors_le
