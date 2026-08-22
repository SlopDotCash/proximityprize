/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R16DiagonalExactValue
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R51UnconditionalQuarticInput

/-!
# LANE B2 (#466 round 51b): THE UNCONDITIONAL r = 2 RUNG — zero named hypotheses

Round 51a discharged the r17 quartic-pairs input at constant 26
(`weilQuarticPairsOn_unconditional`, via the elementary Stepanov milestone).  This brick
replays the r17 moment chain at constant 26 and lands the milestone:

  **`wickAwayAt_two_unconditional`** — at EVERY odd finite field, every nonempty `G` with
  `16·|G|² ≤ √q`, the r = 2 diagonal-subtracted Wick rung
  `WickForIncidenceAwayAt ψ G (QRset χ₂) (insert 0 G) 2` holds.  NO named hypotheses.

The r17 threshold `16·n² ≤ √q` survives unchanged: the constant-26 fourth-moment surplus
`26·n⁴·√q ≤ (26/16)·n²·q` still sits far below the Wick main term (hand-check:
LHS ≈ 5.9·n²·q³ vs RHS ≈ 9.2·n²·q³).  At the prize scaling (`β ≈ 5.3`, so `√q ≈ n^2.65`)
the size condition holds with a large margin.

This is the FIRST fully unconditional nontrivial rung of the corrected (round-16) tower —
the weld of this campaign's Fourier lane with the concurrent Stepanov lane.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 51b, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R51bUnconditionalDeg2Rung

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange
open ArkLib.ProximityGap.Frontier.R16DiagonalExactValue
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R51UnconditionalQuarticInput

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-! ### (1) The constant-26 moment chain (r17 replay, `G`-restricted input). -/

/-- **The `R` second moment at constant 26**: `∑_s R(s)² ≤ 2n²q + 26n⁴√q`. -/
theorem sum_Rker_sq_bound26 (hχ : IsRealQuadChar χ) (G : Finset F)
    (hweil : WeilQuarticPairsOn G χ 26) :
    ∑ s : F, (Rker χ G s) ^ 2
      ≤ 2 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ)
        + 26 * (G.card : ℝ) ^ 4 * Real.sqrt (Fintype.card F) := by
  classical
  set n : ℝ := (G.card : ℝ)
  set q : ℝ := (Fintype.card F : ℝ)
  have hq0 : (0:ℝ) ≤ q := by positivity
  have hs0 : (0:ℝ) ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hexp : ∑ s : F, (Rker χ G s) ^ 2
      = ∑ p ∈ G ×ˢ G, ∑ p' ∈ G ×ˢ G,
          ∑ s : F, (if p.1 = p.2 then 0 else χ (s - p.1) * χ (s - p.2))
            * (if p'.1 = p'.2 then 0 else χ (s - p'.1) * χ (s - p'.2)) := by
    have h1 : ∀ s : F, (Rker χ G s) ^ 2
        = ∑ p ∈ G ×ˢ G, ∑ p' ∈ G ×ˢ G,
            (if p.1 = p.2 then 0 else χ (s - p.1) * χ (s - p.2))
              * (if p'.1 = p'.2 then 0 else χ (s - p'.1) * χ (s - p'.2)) := by
      intro s
      rw [Rker, sq, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl (fun s _ => h1 s), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_comm]
  rw [hexp]
  have hpt : ∀ p ∈ G ×ˢ G, ∀ p' ∈ G ×ˢ G,
      (∑ s : F, (if p.1 = p.2 then 0 else χ (s - p.1) * χ (s - p.2))
        * (if p'.1 = p'.2 then 0 else χ (s - p'.1) * χ (s - p'.2)))
      ≤ ((if p' = p then (1:ℝ) else 0) + (if p' = Prod.swap p then (1:ℝ) else 0)) * q
        + 26 * Real.sqrt q := by
    intro p hpmem p' hp'mem
    by_cases hp : p.1 = p.2
    · have : ∀ s : F, (if p.1 = p.2 then (0:ℝ) else χ (s - p.1) * χ (s - p.2))
          * (if p'.1 = p'.2 then 0 else χ (s - p'.1) * χ (s - p'.2)) = 0 := by
        intro s; simp [hp]
      rw [Finset.sum_congr rfl (fun s _ => this s), Finset.sum_const, smul_zero]
      positivity
    by_cases hp' : p'.1 = p'.2
    · have : ∀ s : F, (if p.1 = p.2 then (0:ℝ) else χ (s - p.1) * χ (s - p.2))
          * (if p'.1 = p'.2 then 0 else χ (s - p'.1) * χ (s - p'.2)) = 0 := by
        intro s; simp [hp']
      rw [Finset.sum_congr rfl (fun s _ => this s), Finset.sum_const, smul_zero]
      positivity
    have hplain : (∑ s : F, (if p.1 = p.2 then (0:ℝ) else χ (s - p.1) * χ (s - p.2))
        * (if p'.1 = p'.2 then 0 else χ (s - p'.1) * χ (s - p'.2)))
        = ∑ s : F, χ (s - p.1) * χ (s - p.2) * (χ (s - p'.1) * χ (s - p'.2)) := by
      exact Finset.sum_congr rfl (fun s _ => by simp [hp, hp'])
    rw [hplain]
    by_cases hmatch : p' = p ∨ p' = Prod.swap p
    · have hterm : ∀ s : F, χ (s - p.1) * χ (s - p.2) * (χ (s - p'.1) * χ (s - p'.2)) ≤ 1 := by
        intro s
        have habs : |χ (s - p.1) * χ (s - p.2) * (χ (s - p'.1) * χ (s - p'.2))| ≤ 1 := by
          rw [abs_mul, abs_mul, abs_mul]
          have a1 := hχ.abs_le_one (s - p.1)
          have a2 := hχ.abs_le_one (s - p.2)
          have a3 := hχ.abs_le_one (s - p'.1)
          have a4 := hχ.abs_le_one (s - p'.2)
          have h12 : |χ (s - p.1)| * |χ (s - p.2)| ≤ 1 := by
            calc |χ (s - p.1)| * |χ (s - p.2)| ≤ 1 * 1 :=
                  mul_le_mul a1 a2 (abs_nonneg _) zero_le_one
              _ = 1 := mul_one 1
          have h34 : |χ (s - p'.1)| * |χ (s - p'.2)| ≤ 1 := by
            calc |χ (s - p'.1)| * |χ (s - p'.2)| ≤ 1 * 1 :=
                  mul_le_mul a3 a4 (abs_nonneg _) zero_le_one
              _ = 1 := mul_one 1
          calc |χ (s - p.1)| * |χ (s - p.2)| * (|χ (s - p'.1)| * |χ (s - p'.2)|)
              ≤ 1 * 1 := mul_le_mul h12 h34 (by positivity) zero_le_one
            _ = 1 := mul_one 1
        exact le_trans (le_abs_self _) habs
      have hsum : (∑ s : F, χ (s - p.1) * χ (s - p.2) * (χ (s - p'.1) * χ (s - p'.2))) ≤ q := by
        calc (∑ s : F, χ (s - p.1) * χ (s - p.2) * (χ (s - p'.1) * χ (s - p'.2)))
            ≤ ∑ _s : F, (1:ℝ) := Finset.sum_le_sum (fun s _ => hterm s)
          _ = q := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
      rcases hmatch with h | h
      · rw [if_pos h]
        have : ((1:ℝ) + (if p' = Prod.swap p then (1:ℝ) else 0)) * q + 26 * Real.sqrt q ≥ q := by
          have hnn : (0:ℝ) ≤ (if p' = Prod.swap p then (1:ℝ) else 0) := by positivity
          nlinarith [hs0, hq0]
        linarith
      · rw [if_pos h]
        have : ((if p' = p then (1:ℝ) else 0) + 1) * q + 26 * Real.sqrt q ≥ q := by
          have hnn : (0:ℝ) ≤ (if p' = p then (1:ℝ) else 0) := by positivity
          nlinarith [hs0, hq0]
        linarith
    · push Not at hmatch
      have h := hweil p hpmem p' hp'mem hp hp' hmatch.1 hmatch.2
      have h1 : (if p' = p then (1:ℝ) else 0) = 0 := if_neg hmatch.1
      have h2 : (if p' = Prod.swap p then (1:ℝ) else 0) = 0 := if_neg hmatch.2
      rw [h1, h2]
      simpa using h
  have htotal : (∑ p ∈ G ×ˢ G, ∑ p' ∈ G ×ˢ G,
      ∑ s : F, (if p.1 = p.2 then 0 else χ (s - p.1) * χ (s - p.2))
        * (if p'.1 = p'.2 then 0 else χ (s - p'.1) * χ (s - p'.2)))
      ≤ ∑ p ∈ G ×ˢ G, ∑ p' ∈ G ×ˢ G,
          (((if p' = p then (1:ℝ) else 0) + (if p' = Prod.swap p then (1:ℝ) else 0)) * q
            + 26 * Real.sqrt q) :=
    Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun p' hp' => hpt p hp p' hp'))
  refine le_trans htotal ?_
  have hinner : ∀ p ∈ G ×ˢ G, ∑ p' ∈ G ×ˢ G,
      (((if p' = p then (1:ℝ) else 0) + (if p' = Prod.swap p then (1:ℝ) else 0)) * q
        + 26 * Real.sqrt q)
      ≤ 2 * q + (n^2) * (26 * Real.sqrt q) := by
    intro p _
    rw [Finset.sum_add_distrib]
    have hc1 : ∑ p' ∈ G ×ˢ G,
        ((if p' = p then (1:ℝ) else 0) + (if p' = Prod.swap p then (1:ℝ) else 0)) * q
        ≤ 2 * q := by
      rw [Finset.sum_congr rfl (fun p' _ => add_mul (if p' = p then (1:ℝ) else 0)
        (if p' = Prod.swap p then (1:ℝ) else 0) q), Finset.sum_add_distrib]
      have e1 : ∑ p' ∈ G ×ˢ G, (if p' = p then (1:ℝ) else 0) * q ≤ q := by
        have hptw : ∀ p' ∈ G ×ˢ G, (if p' = p then (1:ℝ) else 0) * q
            = (if p' = p then q else 0) := by
          intro p' _
          by_cases h : p' = p <;> simp [h]
        rw [Finset.sum_congr rfl hptw, Finset.sum_ite_eq' (G ×ˢ G) p (fun _ => q)]
        by_cases hpG : p ∈ G ×ˢ G
        · rw [if_pos hpG]
        · rw [if_neg hpG]
          positivity
      have e2 : ∑ p' ∈ G ×ˢ G, (if p' = Prod.swap p then (1:ℝ) else 0) * q ≤ q := by
        have hptw : ∀ p' ∈ G ×ˢ G, (if p' = Prod.swap p then (1:ℝ) else 0) * q
            = (if p' = Prod.swap p then q else 0) := by
          intro p' _
          by_cases h : p' = Prod.swap p <;> simp [h]
        rw [Finset.sum_congr rfl hptw, Finset.sum_ite_eq' (G ×ˢ G) (Prod.swap p) (fun _ => q)]
        by_cases hpG : Prod.swap p ∈ G ×ˢ G
        · rw [if_pos hpG]
        · rw [if_neg hpG]
          positivity
      linarith
    have hc2 : ∑ _p' ∈ G ×ˢ G, (26 * Real.sqrt q) = (n^2) * (26 * Real.sqrt q) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_product]
      push_cast [n]
      ring
    rw [hc2]
    linarith [hc1]
  calc (∑ p ∈ G ×ˢ G, ∑ p' ∈ G ×ˢ G,
      (((if p' = p then (1:ℝ) else 0) + (if p' = Prod.swap p then (1:ℝ) else 0)) * q
        + 26 * Real.sqrt q))
      ≤ ∑ _p ∈ G ×ˢ G, (2 * q + (n^2) * (26 * Real.sqrt q)) :=
        Finset.sum_le_sum hinner
    _ = (n^2) * (2 * q + (n^2) * (26 * Real.sqrt q)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_product]
        push_cast [n]
        ring
    _ = 2 * n ^ 2 * q + 26 * n ^ 4 * Real.sqrt q := by ring

/-- **The fourth moment at constant 26**: `∑_s W⁴ ≤ 3n²q + 2n³ + 26n⁴√q`. -/
theorem sum_W_pow_four_bound26 (hχ : IsRealQuadChar χ) (G : Finset F)
    (hweil : WeilQuarticPairsOn G χ 26) :
    ∑ s : F, (Wsum χ G s) ^ 4
      ≤ 3 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) + 2 * (G.card : ℝ) ^ 3
        + 26 * (G.card : ℝ) ^ 4 * Real.sqrt (Fintype.card F) := by
  classical
  set n : ℝ := (G.card : ℝ)
  set q : ℝ := (Fintype.card F : ℝ)
  have hW4 : ∀ s : F, (Wsum χ G s) ^ 4
      = ((n - (if s ∈ G then 1 else 0)) + Rker χ G s) ^ 2 := by
    intro s
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, Wsum_sq_eq hχ G s]
  rw [Finset.sum_congr rfl (fun s _ => hW4 s)]
  have hexp : ∀ s : F, ((n - (if s ∈ G then 1 else 0)) + Rker χ G s) ^ 2
      = (n - (if s ∈ G then 1 else 0)) ^ 2
        + 2 * (n - (if s ∈ G then 1 else 0)) * Rker χ G s + (Rker χ G s) ^ 2 := by
    intro s; ring
  rw [Finset.sum_congr rfl (fun s _ => hexp s), Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have hA : ∑ s : F, (n - (if s ∈ G then 1 else 0)) ^ 2 ≤ n ^ 2 * q := by
    have hpt : ∀ s : F, (n - (if s ∈ G then 1 else 0)) ^ 2 ≤ n ^ 2 := by
      intro s
      have hn0 : (0:ℝ) ≤ n := by positivity
      split_ifs with h
      · have hn1 : (1:ℝ) ≤ n := by
          have h1 : 1 ≤ G.card := Finset.card_pos.mpr ⟨s, h⟩
          have h2 : (1:ℝ) ≤ (G.card : ℝ) := by exact_mod_cast h1
          simpa [n] using h2
        nlinarith
      · nlinarith
    calc ∑ s : F, (n - (if s ∈ G then 1 else 0)) ^ 2 ≤ ∑ _s : F, n ^ 2 :=
          Finset.sum_le_sum (fun s _ => hpt s)
      _ = n ^ 2 * q := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]; ring
  have hB : ∑ s : F, 2 * (n - (if s ∈ G then 1 else 0)) * Rker χ G s ≤ 2 * n ^ 3 := by
    have hsplit : ∀ s : F, 2 * (n - (if s ∈ G then 1 else 0)) * Rker χ G s
        = 2 * n * Rker χ G s - 2 * (if s ∈ G then Rker χ G s else 0) := by
      intro s; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun s _ => hsplit s), Finset.sum_sub_distrib]
    have h1 : ∑ s : F, 2 * n * Rker χ G s ≤ 0 := by
      rw [← Finset.mul_sum]
      have := sum_Rker_nonpos hχ G
      have hn0 : (0:ℝ) ≤ 2 * n := by positivity
      exact mul_nonpos_of_nonneg_of_nonpos hn0 this
    have h2 : -(∑ s : F, 2 * (if s ∈ G then Rker χ G s else 0)) ≤ 2 * n ^ 3 := by
      have habs : |∑ s : F, 2 * (if s ∈ G then Rker χ G s else 0)| ≤ 2 * n ^ 3 := by
        calc |∑ s : F, 2 * (if s ∈ G then Rker χ G s else 0)|
            ≤ ∑ s : F, |2 * (if s ∈ G then Rker χ G s else 0)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ s : F, 2 * (if s ∈ G then n ^ 2 else 0) := by
              refine Finset.sum_le_sum (fun s _ => ?_)
              rw [abs_mul]
              have : |if s ∈ G then Rker χ G s else 0| ≤ (if s ∈ G then n ^ 2 else 0) := by
                split_ifs
                · exact abs_Rker_le hχ G s
                · simp
              calc |(2:ℝ)| * |if s ∈ G then Rker χ G s else 0|
                  ≤ |(2:ℝ)| * (if s ∈ G then n ^ 2 else 0) :=
                    mul_le_mul_of_nonneg_left this (abs_nonneg 2)
                _ = 2 * (if s ∈ G then n ^ 2 else 0) := by norm_num
          _ = 2 * n ^ 3 := by
              rw [← Finset.mul_sum]
              have : ∑ s : F, (if s ∈ G then n ^ 2 else 0) = n * n ^ 2 := by
                rw [Finset.sum_ite_mem Finset.univ G (fun _ => n ^ 2)]
                rw [Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
                try ring
              calc 2 * ∑ s : F, (if s ∈ G then n ^ 2 else 0)
                  = 2 * (n * n ^ 2) := by rw [this]
                _ = 2 * n ^ 3 := by ring
      linarith [neg_abs_le (∑ s : F, 2 * (if s ∈ G then Rker χ G s else 0)), habs]
    linarith
  have hC := sum_Rker_sq_bound26 hχ G hweil
  have := add_le_add (add_le_add hA hB) hC
  calc (∑ s : F, (n - (if s ∈ G then 1 else 0)) ^ 2)
        + (∑ s : F, 2 * (n - (if s ∈ G then 1 else 0)) * Rker χ G s)
        + ∑ s : F, (Rker χ G s) ^ 2
      ≤ n ^ 2 * q + 2 * n ^ 3 + (2 * n ^ 2 * q + 26 * n ^ 4 * Real.sqrt q) := this
    _ = 3 * n ^ 2 * q + 2 * n ^ 3 + 26 * n ^ 4 * Real.sqrt q := by ring

/-- **The third moment at constant 26 via Cauchy–Schwarz**:
`|∑_s W³| ≤ n² + √(nq·(2n²q + 26n⁴√q))`. -/
theorem sum_W_cubed_bound26 (hχ : IsRealQuadChar χ) (G : Finset F)
    (hweil : WeilQuarticPairsOn G χ 26) :
    |∑ s : F, (Wsum χ G s) ^ 3|
      ≤ (G.card : ℝ) ^ 2
        + Real.sqrt ((G.card : ℝ) * (Fintype.card F : ℝ)
            * (2 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ)
              + 26 * (G.card : ℝ) ^ 4 * Real.sqrt (Fintype.card F))) := by
  classical
  set n : ℝ := (G.card : ℝ)
  set q : ℝ := (Fintype.card F : ℝ)
  have hsplit : ∀ s : F, (Wsum χ G s) ^ 3
      = Wsum χ G s * (n - (if s ∈ G then 1 else 0)) + Wsum χ G s * Rker χ G s := by
    intro s
    have := Wsum_sq_eq hχ G s
    calc (Wsum χ G s) ^ 3 = Wsum χ G s * (Wsum χ G s) ^ 2 := by ring
      _ = Wsum χ G s * ((n - (if s ∈ G then 1 else 0)) + Rker χ G s) := by rw [this]
      _ = _ := by ring
  rw [Finset.sum_congr rfl (fun s _ => hsplit s), Finset.sum_add_distrib]
  have hT1 : |∑ s : F, Wsum χ G s * (n - (if s ∈ G then 1 else 0))| ≤ n ^ 2 := by
    have hpt : ∀ s : F, Wsum χ G s * (n - (if s ∈ G then 1 else 0))
        = n * Wsum χ G s - (if s ∈ G then Wsum χ G s else 0) := by
      intro s; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun s _ => hpt s), Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, sum_W hχ G, mul_zero]
    rw [zero_sub, abs_neg]
    calc |∑ s : F, (if s ∈ G then Wsum χ G s else 0)|
        ≤ ∑ s : F, |if s ∈ G then Wsum χ G s else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s : F, (if s ∈ G then n else 0) := by
          refine Finset.sum_le_sum (fun s _ => ?_)
          split_ifs
          · exact abs_Wsum_le hχ G s
          · simp
      _ = n ^ 2 := by
          rw [Finset.sum_ite_mem Finset.univ G (fun _ => n)]
          rw [Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
          ring
  have hT2 : |∑ s : F, Wsum χ G s * Rker χ G s|
      ≤ Real.sqrt (n * q * (2 * n ^ 2 * q + 26 * n ^ 4 * Real.sqrt q)) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun s => Wsum χ G s)
      (fun s => Rker χ G s)
    have hW2 : ∑ s : F, (Wsum χ G s) ^ 2 ≤ n * q := by
      rw [sum_W_sq hχ G]
      have hn0 : (0:ℝ) ≤ n := by positivity
      nlinarith [hn0, Finset.card_le_univ G, (by exact_mod_cast Finset.card_le_univ G :
        (G.card : ℝ) ≤ (Fintype.card F : ℝ))]
    have hR2 := sum_Rker_sq_bound26 hχ G hweil
    have hsq : (∑ s : F, Wsum χ G s * Rker χ G s) ^ 2
        ≤ n * q * (2 * n ^ 2 * q + 26 * n ^ 4 * Real.sqrt q) := by
      have hprod : (∑ s : F, (Wsum χ G s) ^ 2) * (∑ s : F, (Rker χ G s) ^ 2)
          ≤ (n * q) * (2 * n ^ 2 * q + 26 * n ^ 4 * Real.sqrt q) := by
        have h1 : (0:ℝ) ≤ ∑ s : F, (Rker χ G s) ^ 2 := by positivity
        have h2 : (0:ℝ) ≤ n * q := by positivity
        exact mul_le_mul hW2 hR2 h1 h2
      calc (∑ s : F, Wsum χ G s * Rker χ G s) ^ 2
          ≤ (∑ s : F, (Wsum χ G s) ^ 2) * (∑ s : F, (Rker χ G s) ^ 2) := hcs
        _ ≤ _ := hprod
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  calc |(∑ s : F, Wsum χ G s * (n - (if s ∈ G then 1 else 0)))
        + ∑ s : F, Wsum χ G s * Rker χ G s|
      ≤ |∑ s : F, Wsum χ G s * (n - (if s ∈ G then 1 else 0))|
        + |∑ s : F, Wsum χ G s * Rker χ G s| := abs_add_le _ _
    _ ≤ n ^ 2 + Real.sqrt (n * q * (2 * n ^ 2 * q + 26 * n ^ 4 * Real.sqrt q)) :=
        add_le_add hT1 hT2

/-! ### (2) The rung at constant 26, then THE UNCONDITIONAL MILESTONE. -/

set_option maxHeartbeats 3200000 in
-- The replayed r17 polynomial inequality needs a larger heartbeat budget for `nlinarith`.
/-- The r17 rung replayed at input constant 26, same threshold `16·n² ≤ √q`. -/
theorem wickAwayAt_two_of_weil26 (hχ : IsRealQuadChar χ)
    [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hweil : WeilQuarticPairsOn G χ 26)
    (hbig : 16 * (G.card : ℝ) ^ 2 ≤ Real.sqrt (Fintype.card F))
    (hGne : G.Nonempty) :
    WickForIncidenceAwayAt ψ G (QRset χ) (insert (0:F) G) 2 := by
  classical
  set n : ℝ := (G.card : ℝ) with hn_def
  set q : ℝ := (Fintype.card F : ℝ) with hq_def
  set sq : ℝ := Real.sqrt q with hsq_def
  have hn1 : (1:ℝ) ≤ n := by
    have h1 : 1 ≤ G.card := Finset.card_pos.mpr hGne
    have h2 : (1:ℝ) ≤ (G.card : ℝ) := by exact_mod_cast h1
    simpa [hn_def] using h2
  have hq1 : (1:ℝ) ≤ q := by
    have h1 : 1 ≤ Fintype.card F := Fintype.card_pos
    have h2 : (1:ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast h1
    simpa [hq_def] using h2
  have hsq0 : (0:ℝ) ≤ sq := Real.sqrt_nonneg q
  have hsqq : sq ^ 2 = q := Real.sq_sqrt (by linarith)
  have hsq16 : 16 * n ^ 2 ≤ sq := hbig
  have hsq1 : (1:ℝ) ≤ sq := by nlinarith [hn1, hsq16]
  set x : ℝ := (gSum χ ψ).re with hx_def
  have hgnorm : ‖gSum χ ψ‖ ^ 2 = q := norm_gSum_sq hχ hψ
  have hx2 : x ^ 2 ≤ q := by
    have h1 : x ^ 2 ≤ ‖gSum χ ψ‖ ^ 2 := by
      have := Complex.abs_re_le_norm (gSum χ ψ)
      have hx0 : |x| ≤ ‖gSum χ ψ‖ := by simpa [hx_def] using this
      nlinarith [hx0, abs_nonneg x, sq_abs x]
    linarith [hgnorm ▸ h1]
  have hxabs : |x| ≤ sq := by
    have h1 : x ^ 2 ≤ sq ^ 2 := by rw [hsqq]; exact hx2
    nlinarith [sq_abs x, h1, abs_nonneg x, hsq0]
  have hIsq : ∀ s : F, s ∉ (insert (0:F) G) →
      ‖incidenceSum ψ G (QRset χ) s‖ ^ 2
        = (q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2) / 4 := by
    intro s hs
    have hsG : s ∉ G := fun h => hs (Finset.mem_insert_of_mem h)
    have hbr := bridge hχ hψ G s
    rw [if_neg hsG] at hbr
    have hI : incidenceSum ψ G (QRset χ) s
        = (gSum χ ψ * ((Wsum χ G s : ℝ) : ℂ) - (G.card : ℂ)) / 2 := by
      rw [hbr]; ring
    rw [hI]
    have h2n : ‖(2:ℂ)‖ = 2 := by norm_num
    rw [norm_div, norm_sub_rev, div_pow, h2n]
    have hz : ‖(G.card : ℂ) - gSum χ ψ * ((Wsum χ G s : ℝ) : ℂ)‖ ^ 2
        = q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2 := by
      set W : ℝ := Wsum χ G s
      have hre : ((G.card : ℂ) - gSum χ ψ * ((W : ℝ) : ℂ)).re = n - x * W := by
        simp [Complex.sub_re, Complex.mul_re, hx_def, hn_def]
      have him : ((G.card : ℂ) - gSum χ ψ * ((W : ℝ) : ℂ)).im = -((gSum χ ψ).im * W) := by
        simp [Complex.sub_im, Complex.mul_im]
      rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
      have hxy : x ^ 2 + (gSum χ ψ).im ^ 2 = q := by
        have := Complex.sq_norm (gSum χ ψ)
        have h2 : Complex.normSq (gSum χ ψ) = q := by
          rw [← this, hgnorm]
        rw [Complex.normSq_apply] at h2
        nlinarith [h2]
      nlinarith [hxy]
    rw [hz]
    norm_num
  have hstep2 : incidenceMomentAway ψ G (QRset χ) (insert (0:F) G) 2
      ≤ (∑ s : F, (q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2) ^ 2) / 16 := by
    unfold incidenceMomentAway
    have hpt : ∀ s ∈ Finset.univ \ (insert (0:F) G),
        ‖incidenceSum ψ G (QRset χ) s‖ ^ (2 * 2)
          = ((q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2) / 4) ^ 2 := by
      intro s hs
      have hs' : s ∉ (insert (0:F) G) := (Finset.mem_sdiff.mp hs).2
      rw [pow_mul, hIsq s hs']
    rw [Finset.sum_congr rfl hpt]
    have hsub : ∑ s ∈ Finset.univ \ (insert (0:F) G),
        ((q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2) / 4) ^ 2
        ≤ ∑ s : F, ((q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2) / 4) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
        (fun s _ _ => by positivity)
    refine le_trans hsub (le_of_eq ?_)
    have hshape : ∀ s : F,
        ((q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2) / 4) ^ 2
          = (q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2) ^ 2 / 16 := by
      intro s; ring
    rw [Finset.sum_congr rfl (fun s _ => hshape s), ← Finset.sum_div]
  have hW2 := sum_W_sq hχ G
  have hW1 := sum_W hχ G
  have hW4 := sum_W_pow_four_bound26 hχ G hweil
  have hW3 := sum_W_cubed_bound26 hχ G hweil
  have hexpand : ∑ s : F, (q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2) ^ 2
      = q ^ 2 * (∑ s : F, (Wsum χ G s) ^ 4)
        + (4 * n ^ 2 * x ^ 2 + 2 * q * n ^ 2) * (∑ s : F, (Wsum χ G s) ^ 2)
        + q * n ^ 4
        - 4 * n * q * x * (∑ s : F, (Wsum χ G s) ^ 3)
        - 4 * n ^ 3 * x * (∑ s : F, Wsum χ G s) := by
    have hpt : ∀ s : F, (q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2) ^ 2
        = q ^ 2 * (Wsum χ G s) ^ 4
          + (4 * n ^ 2 * x ^ 2 + 2 * q * n ^ 2) * (Wsum χ G s) ^ 2
          + n ^ 4
          - 4 * n * q * x * (Wsum χ G s) ^ 3
          - 4 * n ^ 3 * x * Wsum χ G s := by
      intro s; ring
    rw [Finset.sum_congr rfl (fun s _ => hpt s)]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  set SW4 : ℝ := ∑ s : F, (Wsum χ G s) ^ 4
  set SW3 : ℝ := ∑ s : F, (Wsum χ G s) ^ 3
  have hbound : ∑ s : F, (q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2) ^ 2
      ≤ q ^ 2 * (3 * n ^ 2 * q + 2 * n ^ 3 + 26 * n ^ 4 * sq)
        + (4 * n ^ 2 * q + 2 * q * n ^ 2) * (n * q)
        + q * n ^ 4
        + 4 * n * q * sq * (n ^ 2 + Real.sqrt (n * q * (2 * n ^ 2 * q + 26 * n ^ 4 * sq))) := by
    rw [hexpand, hW1, hW2]
    have hSW4nn : (0:ℝ) ≤ q ^ 2 := by positivity
    have b1 : q ^ 2 * SW4 ≤ q ^ 2 * (3 * n ^ 2 * q + 2 * n ^ 3 + 26 * n ^ 4 * sq) :=
      mul_le_mul_of_nonneg_left hW4 hSW4nn
    have b2 : (4 * n ^ 2 * x ^ 2 + 2 * q * n ^ 2) * (n * (q - n))
        ≤ (4 * n ^ 2 * q + 2 * q * n ^ 2) * (n * q) := by
      have hc1 : 4 * n ^ 2 * x ^ 2 + 2 * q * n ^ 2 ≤ 4 * n ^ 2 * q + 2 * q * n ^ 2 := by
        nlinarith [hx2, hn1]
      have hc2 : n * (q - n) ≤ n * q := by nlinarith [hn1]
      have hc3 : (0:ℝ) ≤ n * (q - n) := by
        have hnq : n ≤ q := by
          have h1 : G.card ≤ Fintype.card F := Finset.card_le_univ G
          have h2 : (G.card : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast h1
          simpa [hn_def, hq_def] using h2
        nlinarith [hn1]
      have hc4 : (0:ℝ) ≤ 4 * n ^ 2 * x ^ 2 + 2 * q * n ^ 2 := by positivity
      calc (4 * n ^ 2 * x ^ 2 + 2 * q * n ^ 2) * (n * (q - n))
          ≤ (4 * n ^ 2 * q + 2 * q * n ^ 2) * (n * (q - n)) :=
            mul_le_mul_of_nonneg_right hc1 hc3
        _ ≤ (4 * n ^ 2 * q + 2 * q * n ^ 2) * (n * q) := by
            have : (0:ℝ) ≤ 4 * n ^ 2 * q + 2 * q * n ^ 2 := by positivity
            exact mul_le_mul_of_nonneg_left hc2 this
    have b3 : -(4 * n * q * x * SW3) ≤ 4 * n * q * sq
        * (n ^ 2 + Real.sqrt (n * q * (2 * n ^ 2 * q + 26 * n ^ 4 * sq))) := by
      have habs : |4 * n * q * x * SW3| ≤ 4 * n * q * sq
          * (n ^ 2 + Real.sqrt (n * q * (2 * n ^ 2 * q + 26 * n ^ 4 * sq))) := by
        rw [abs_mul]
        have h1 : |4 * n * q * x| ≤ 4 * n * q * sq := by
          rw [abs_mul]
          have : |(4 * n * q : ℝ)| = 4 * n * q := abs_of_nonneg (by positivity)
          rw [this]
          exact mul_le_mul_of_nonneg_left hxabs (by positivity)
        have h2 : |SW3| ≤ n ^ 2 + Real.sqrt (n * q * (2 * n ^ 2 * q + 26 * n ^ 4 * sq)) := hW3
        have h3 : (0:ℝ) ≤ |SW3| := abs_nonneg _
        calc |4 * n * q * x| * |SW3| ≤ (4 * n * q * sq) * |SW3| :=
              mul_le_mul_of_nonneg_right h1 h3
          _ ≤ (4 * n * q * sq)
              * (n ^ 2 + Real.sqrt (n * q * (2 * n ^ 2 * q + 26 * n ^ 4 * sq))) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
      linarith [neg_abs_le (4 * n * q * x * SW3), habs]
    nlinarith [b1, b2, b3]
  have hqr := qr_weight_lower hχ (χ := χ) hψ G
  unfold WickForIncidenceAwayAt
  have hdf : (Nat.doubleFactorial (2 * 2 - 1) : ℝ) = 3 := by
    have h3 : Nat.doubleFactorial (2 * 2 - 1) = 3 := by decide
    rw [h3]; norm_num
  rw [hdf]
  have hnq : n ≤ q := by
    have h1 : G.card ≤ Fintype.card F := Finset.card_le_univ G
    have h2 : (G.card : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast h1
    simpa [hn_def, hq_def] using h2
  have hL : (0:ℝ) ≤ (q * n - n ^ 2 - n ^ 2 * sq) / 2 := by
    have h1 : n ^ 2 * sq ≤ (sq / 16) * sq := by
      have : n ^ 2 ≤ sq / 16 := by linarith [hsq16]
      exact mul_le_mul_of_nonneg_right this hsq0
    have h2 : (sq / 16) * sq = q / 16 := by
      have : sq * sq = q := by nlinarith [hsqq]
      nlinarith [this]
    have h3 : n ^ 2 ≤ q / 16 := by
      have h4 : n ^ 2 ≤ sq / 16 := by linarith [hsq16]
      have h5 : sq ≤ q := by nlinarith [hsq1, hsqq]
      linarith
    have h6 : q * 1 ≤ q * n := mul_le_mul_of_nonneg_left hn1 (by linarith : (0:ℝ) ≤ q)
    nlinarith [hn1, hq1, h1, h2, h3, h6]
  have hwick_lower : q * 3 * ((q * n - n ^ 2 - n ^ 2 * sq) / 2) ^ 2
      ≤ q * 3 * (∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ 2 := by
    have h2 : (0:ℝ) ≤ ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2 := by positivity
    have h3 : ((q * n - n ^ 2 - n ^ 2 * sq) / 2) ^ 2
        ≤ (∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ 2 := by
      have hle : (q * n - n ^ 2 - n ^ 2 * sq) / 2 ≤ ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2 := hqr
      nlinarith [hL, hle, h2]
    have h4 : (0:ℝ) ≤ q * 3 := by positivity
    exact mul_le_mul_of_nonneg_left h3 h4
  -- CS-sqrt simplification at constant 26: √(nq(2n²q + 26n⁴·sq)) ≤ 2n²q
  have hcs_bound : Real.sqrt (n * q * (2 * n ^ 2 * q + 26 * n ^ 4 * sq)) ≤ 2 * n ^ 2 * q := by
    have h1 : n ^ 2 ≤ sq / 16 := by linarith [hsq16]
    have h2 : n ^ 5 * sq ≤ n ^ 3 * q / 16 := by
      have h3 : n ^ 2 * sq ≤ (sq / 16) * sq := mul_le_mul_of_nonneg_right h1 hsq0
      have h4 : (sq / 16) * sq = q / 16 := by nlinarith [hsqq]
      have h5 : n ^ 5 * sq = n ^ 3 * (n ^ 2 * sq) := by ring
      have h6 : (0:ℝ) ≤ n ^ 3 := by positivity
      calc n ^ 5 * sq = n ^ 3 * (n ^ 2 * sq) := h5
        _ ≤ n ^ 3 * (q / 16) := mul_le_mul_of_nonneg_left (by linarith [h3, h4]) h6
        _ = n ^ 3 * q / 16 := by ring
    have harg : n * q * (2 * n ^ 2 * q + 26 * n ^ 4 * sq) ≤ (2 * n ^ 2 * q) ^ 2 := by
      -- 2n³q² + 26·n⁵·q·sq ≤ 2n⁴q² + (26/16)n³q² ≤ 4n⁴q²
      have h7 : 26 * q * (n ^ 5 * sq) ≤ 26 * q * (n ^ 3 * q / 16) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have h8 : n ^ 3 * q ^ 2 ≤ n ^ 4 * q ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (by positivity : (0:ℝ) ≤ n ^ 3 * q ^ 2)]
      nlinarith [h7, h8, hn1, hq1]
    calc Real.sqrt (n * q * (2 * n ^ 2 * q + 26 * n ^ 4 * sq))
        ≤ Real.sqrt ((2 * n ^ 2 * q) ^ 2) := Real.sqrt_le_sqrt harg
      _ = 2 * n ^ 2 * q := Real.sqrt_sq (by positivity)
  have hbound2 : ∑ s : F, (q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2) ^ 2
      ≤ q ^ 2 * (3 * n ^ 2 * q + 2 * n ^ 3 + 26 * n ^ 4 * sq)
        + (4 * n ^ 2 * q + 2 * q * n ^ 2) * (n * q)
        + q * n ^ 4
        + 4 * n * q * sq * (n ^ 2 + 2 * n ^ 2 * q) := by
    refine le_trans hbound ?_
    have h0 : (0:ℝ) ≤ 4 * n * q * sq := by positivity
    have := mul_le_mul_of_nonneg_left
      (by linarith [hcs_bound] :
        n ^ 2 + Real.sqrt (n * q * (2 * n ^ 2 * q + 26 * n ^ 4 * sq)) ≤ n ^ 2 + 2 * n ^ 2 * q)
      h0
    linarith [this]
  -- THE POLYNOMIAL INEQUALITY at constant 26 (q = sq², sq ≥ 16n², n ≥ 1)
  have hpoly : q ^ 2 * (3 * n ^ 2 * q + 2 * n ^ 3 + 26 * n ^ 4 * sq)
        + (4 * n ^ 2 * q + 2 * q * n ^ 2) * (n * q)
        + q * n ^ 4
        + 4 * n * q * sq * (n ^ 2 + 2 * n ^ 2 * q)
      ≤ 16 * (q * 3 * ((q * n - n ^ 2 - n ^ 2 * sq) / 2) ^ 2) := by
    have e1 : q = sq ^ 2 := hsqq.symm
    rw [e1]
    have k1 : 16 * n ^ 4 * sq ^ 5 ≤ n ^ 2 * sq ^ 6 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsq16) (by positivity : (0:ℝ) ≤ n ^ 2 * sq ^ 5)]
    have k2 : 16 * n ^ 3 * sq ^ 5 ≤ n * sq ^ 6 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsq16) (by positivity : (0:ℝ) ≤ n * sq ^ 5)]
    have k3 : 16 * n ^ 3 * sq ^ 4 ≤ n * sq ^ 5 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsq16) (by positivity : (0:ℝ) ≤ n * sq ^ 4)]
    have k4 : 16 * n ^ 3 * sq ^ 3 ≤ n * sq ^ 4 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsq16) (by positivity : (0:ℝ) ≤ n * sq ^ 3)]
    have k5 : n * sq ^ 6 ≤ n ^ 2 * sq ^ 6 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (by positivity : (0:ℝ) ≤ sq ^ 6)]
    have k6 : n * sq ^ 5 ≤ n ^ 2 * sq ^ 6 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsq1) (by positivity : (0:ℝ) ≤ n * sq ^ 5), k5,
        mul_nonneg (sub_nonneg.mpr hn1) (by positivity : (0:ℝ) ≤ sq ^ 5)]
    have k7 : n * sq ^ 4 ≤ n ^ 2 * sq ^ 6 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsq1) (by positivity : (0:ℝ) ≤ n * sq ^ 4), k6,
        mul_nonneg (sub_nonneg.mpr hsq1) (by positivity : (0:ℝ) ≤ n * sq ^ 5)]
    have k8 : (0:ℝ) ≤ n ^ 4 * sq ^ 4 := by positivity
    have k9 : (0:ℝ) ≤ n ^ 4 * sq ^ 3 := by positivity
    have k10 : (0:ℝ) ≤ n ^ 4 * sq ^ 2 := by positivity
    nlinarith [k1, k2, k3, k4, k5, k6, k7, k8, k9, k10]
  calc incidenceMomentAway ψ G (QRset χ) (insert (0:F) G) 2
      ≤ (∑ s : F, (q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2) ^ 2) / 16 := hstep2
    _ ≤ (q ^ 2 * (3 * n ^ 2 * q + 2 * n ^ 3 + 26 * n ^ 4 * sq)
          + (4 * n ^ 2 * q + 2 * q * n ^ 2) * (n * q)
          + q * n ^ 4
          + 4 * n * q * sq * (n ^ 2 + 2 * n ^ 2 * q)) / 16 := by
        gcongr
    _ ≤ q * 3 * ((q * n - n ^ 2 - n ^ 2 * sq) / 2) ^ 2 := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 16)]
        linarith [hpoly]
    _ ≤ q * 3 * (∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ 2 := hwick_lower
    _ = (Fintype.card F : ℝ) * 3 * (∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ 2 := by
        rw [hq_def]

/-- **THE UNCONDITIONAL r = 2 RUNG (round-51 milestone).**  At every odd finite field,
every nonempty `G` with `16·|G|² ≤ √q`, the diagonal-subtracted r = 2 Wick rung holds for
the concrete quadratic character.  ZERO named hypotheses — the weld of the Fourier lane
(r16/r17) with the elementary Stepanov lane (r23-milestone). -/
theorem wickAwayAt_two_unconditional (hF : ringChar F ≠ 2)
    [DecidablePred fun b : F => realQuadChar F b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hbig : 16 * (G.card : ℝ) ^ 2 ≤ Real.sqrt (Fintype.card F))
    (hGne : G.Nonempty) :
    WickForIncidenceAwayAt ψ G (QRset (realQuadChar F)) (insert (0:F) G) 2 :=
  wickAwayAt_two_of_weil26 (isRealQuadChar_realQuadChar hF) hψ G
    (weilQuarticPairsOn_unconditional hF G) hbig hGne

/-- Constant-relaxed consumer form of `wickAwayAt_two_unconditional`.  Any downstream lane
that tracks the corrected away-Wick rung with slack `C ≥ 1` can consume the unconditional
quadratic-character r = 2 milestone directly. -/
theorem wickAwayAtWithConstant_two_unconditional (hF : ringChar F ≠ 2)
    [DecidablePred fun b : F => realQuadChar F b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {C : ℝ} (hC : 1 ≤ C)
    (hbig : 16 * (G.card : ℝ) ^ 2 ≤ Real.sqrt (Fintype.card F))
    (hGne : G.Nonempty) :
    WickAwayAtWithConstant ψ G (QRset (realQuadChar F)) (insert (0:F) G) 2 C :=
  wickAwayAtWithConstant_of_wickForIncidenceAwayAt
    G (QRset (realQuadChar F)) (insert (0:F) G) 2 hC
    (wickAwayAt_two_unconditional hF hψ G hbig hGne)

/-- Raw fourth-moment target supplied unconditionally by the r = 2 quadratic-character rung. -/
theorem rawFourthMomentWithDiagonal_two_unconditional (hF : ringChar F ≠ 2)
    [DecidablePred fun b : F => realQuadChar F b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hbig : 16 * (G.card : ℝ) ^ 2 ≤ Real.sqrt (Fintype.card F))
    (hGne : G.Nonempty) :
    RawFourthMomentWithDiagonal ψ G (QRset (realQuadChar F)) (insert (0:F) G) :=
  (wickForIncidenceAwayAt_two_iff_rawFourthMomentWithDiagonal G
    (QRset (realQuadChar F)) (insert (0:F) G)).mp
    (wickAwayAt_two_unconditional hF hψ G hbig hGne)

end ArkLib.ProximityGap.Frontier.R51bUnconditionalDeg2Rung

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R51bUnconditionalDeg2Rung.sum_Rker_sq_bound26
#print axioms ArkLib.ProximityGap.Frontier.R51bUnconditionalDeg2Rung.sum_W_pow_four_bound26
#print axioms ArkLib.ProximityGap.Frontier.R51bUnconditionalDeg2Rung.sum_W_cubed_bound26
#print axioms ArkLib.ProximityGap.Frontier.R51bUnconditionalDeg2Rung.wickAwayAt_two_of_weil26
#print axioms
  ArkLib.ProximityGap.Frontier.R51bUnconditionalDeg2Rung.wickAwayAt_two_unconditional
#print axioms
  ArkLib.ProximityGap.Frontier.R51bUnconditionalDeg2Rung.wickAwayAtWithConstant_two_unconditional
#print axioms
  ArkLib.ProximityGap.Frontier.R51bUnconditionalDeg2Rung.rawFourthMomentWithDiagonal_two_unconditional
