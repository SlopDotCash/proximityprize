/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodCosetReduction

/-!
# The Parseval floor on the subgroup Gauss-sum sup-norm (#407)

The per-frequency core `M(n) = max_{b≠0} ‖η_b‖` (`= λ₂(Cay(F_q, μ_n))`, the generalized-Paley graph
second eigenvalue) is bounded **below** by the average over nonzero frequencies, directly from the
landed second moment `∑_b ‖η_b‖² = q·|G|`:

> there is `b ≠ 0` with  `‖η_b‖² ≥ (q·n − n²)/(q − 1) = n·(q − n)/(q − 1)`,  `n = |G|`, `q = |F|`.

So `M(n) ≥ √(n(q−n)/(q−1)) ≈ √n` — the floor scale `√n` is **unavoidable** (the Alon–Boppana side of
the spectral frame). This is the *proven lower half* of the spectral lever for `δ*`: the prize needs the
matching **upper** bound `M(n) ≤ C·√(n·log(1/ε*))` (the open BGK / Paley-graph sub-`√q` cancellation,
kept as a named-open Prop). Establishing the two-sided frame is the recommended attack surface (#407
24-connection ledger, lever D): floor `√n` proven here, ceiling open.

Axiom-clean. Issue #407.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.GaussPeriodCosetReduction

namespace ArkLib.ProximityGap.GaussPeriodParsevalFloor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Sum of the squared periods over the nonzero frequencies:** `∑_{b≠0} ‖η_b‖² = q·n − n²`
(`= (q − n)·n`), from the second moment `∑_b ‖η_b‖² = q·n` minus `‖η_0‖² = n²`. -/
theorem sum_sq_erase_zero {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2
      = (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 := by
  have h2 : ∑ b : F, ‖eta ψ G b‖ ^ 2 = (Fintype.card F : ℝ) * G.card :=
    subgroup_gaussSum_secondMoment hψ G
  have hz : ‖eta ψ G (0 : F)‖ ^ 2 = (G.card : ℝ) ^ 2 := by
    rw [eta_zero, Complex.norm_natCast]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0), h2, hz]

/-- **The Parseval floor.** Some nonzero frequency has squared period at least the nonzero average
`n(q−n)/(q−1)`; hence `M(n) = max_{b≠0}‖η_b‖ ≥ √(n(q−n)/(q−1)) ≈ √n`. The `√n` floor scale is
unavoidable — the proven (lower) half of the spectral `δ*` frame. -/
theorem exists_eta_sq_ge_parseval_floor {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : 2 ≤ Fintype.card F) :
    ∃ b : F, b ≠ 0 ∧
      ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) / ((Fintype.card F : ℝ) - 1)
        ≤ ‖eta ψ G b‖ ^ 2 := by
  classical
  set s : Finset F := Finset.univ.erase (0 : F) with hs
  have hscard : (s.card : ℝ) = (Fintype.card F : ℝ) - 1 := by
    rw [hs, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
    have : 1 ≤ Fintype.card F := le_trans (by norm_num) hq
    push_cast [Nat.cast_sub this]; ring
  have hsne : s.Nonempty := by
    rw [hs]; rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
    omega
  have hsum : ∑ b ∈ s, ‖eta ψ G b‖ ^ 2 = (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 :=
    sum_sq_erase_zero hψ G
  -- pigeonhole: some term ≥ average
  by_contra hcon
  push_neg at hcon
  set avg : ℝ := ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) / ((Fintype.card F : ℝ) - 1)
    with havg
  have hlt : ∀ b ∈ s, ‖eta ψ G b‖ ^ 2 < avg := by
    intro b hb
    have hbne : b ≠ 0 := Finset.ne_of_mem_erase hb
    exact hcon b hbne
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) - 1 := by
    have : (2 : ℝ) ≤ Fintype.card F := by exact_mod_cast hq
    linarith
  have hsumlt : ∑ b ∈ s, ‖eta ψ G b‖ ^ 2 < ∑ _b ∈ s, avg :=
    Finset.sum_lt_sum_of_nonempty hsne hlt
  rw [Finset.sum_const, nsmul_eq_mul, hscard] at hsumlt
  have hcancel : ((Fintype.card F : ℝ) - 1) * avg
      = (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 := by
    rw [havg]; field_simp
  rw [hcancel, hsum] at hsumlt
  exact lt_irrefl _ hsumlt

end ArkLib.ProximityGap.GaussPeriodParsevalFloor

#print axioms ArkLib.ProximityGap.GaussPeriodParsevalFloor.sum_sq_erase_zero
#print axioms ArkLib.ProximityGap.GaussPeriodParsevalFloor.exists_eta_sq_ge_parseval_floor
