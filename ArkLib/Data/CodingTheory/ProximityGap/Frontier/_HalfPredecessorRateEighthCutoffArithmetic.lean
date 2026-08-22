/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R387RateEighthPruning

/-!
# Rate-`1/8` Johnson strata at the intrinsic pruning cutoff

The canonical rate-`1/8` pruning argument only needs `h >= 1699` to turn
`5 * |R| <= 3 * h + 972` into `7 * |R| <= 5 * h`, using that `|R|` is an
integer.  The arithmetic envelope still fails at `h = 1698`.  The first implementation
used the round production cutoff `h >= 2048` in its residue-uniform Johnson
lemmas as well.  This file separates the arithmetic: the exceptional-core
bound needs no scale assumption beyond the nonzero-rate hypotheses, while
the ultra-core bound already holds at `h >= 416`.
-/

set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthCutoffArithmetic

open ArkLib.ProximityGap.Frontier.R387RateEighthPruning

/-! ## Exact integer union cutoff -/

/-- The weighted exceptional-union envelope closes from `h = 1699` once the
union cardinality is kept integral. -/
theorem seven_mul_le_five_mul_of_union_envelope
    {h R : ℕ} (hh : 1699 ≤ h) (hfive : 5 * R ≤ 3 * h + 972) :
    7 * R ≤ 5 * h := by
  by_contra hnot
  have hstrict : 5 * h < 7 * R := by omega
  have hupper : h ≤ 1699 := by nlinarith
  have heq : h = 1699 := by omega
  subst h
  omega

/-- The same numerical envelope does not imply the target at `h = 1698`:
`R = 1213` is the exact integer obstruction. -/
theorem union_envelope_cutoff_sharp :
    5 * 1213 ≤ 3 * 1698 + 972 ∧ 5 * 1698 < 7 * 1213 := by
  norm_num

/-- Residue-uniform exceptional-core Johnson bound.  The rate hypotheses
already force `floor(h / 4) >= 1`; no production-scale cutoff is needed. -/
theorem exceptional_core_family_card_le_fifteen_generic
    {U Line : Type*} [Fintype U] [DecidableEq U] [DecidableEq Line]
    (h k : ℕ) (hk : 1 ≤ k) (hrate : 4 * k ≤ h)
    (hU : Fintype.card U = 2 * h)
    (E : Finset Line) (core : Line → Finset U)
    (hsize : ∀ line ∈ E, 3 * (h / 4) + 2 ≤ (core line).card)
    (hinter : ∀ line ∈ E, ∀ line' ∈ E, line ≠ line' →
      (core line ∩ core line').card ≤ k - 1) :
    E.card ≤ 15 := by
  let q := h / 4
  have hq : 1 ≤ q := by
    dsimp only [q]
    omega
  have hkq : k ≤ q := by
    dsimp only [q]
    omega
  have hdZ : k - 1 ≤ 3 * q + 2 := by omega
  have hJ := johnson_core_packing
    E core (3 * q + 2) (k - 1) hdZ
      (by simpa only [q] using hsize) hinter
  rw [hU] at hJ
  by_contra hnot
  have hE : 16 ≤ E.card := by omega
  have hhq : 4 * q ≤ h := by
    dsimp only [q]
    omega
  have hhq' : h ≤ 4 * q + 3 := by
    dsimp only [q]
    omega
  have hkpredCast : ((k - 1 : ℕ) : ℝ) ≤ (q : ℝ) - 1 := by
    rw [Nat.cast_sub hk, Nat.cast_one]
    have hkqR : (k : ℝ) ≤ q := by exact_mod_cast hkq
    linarith
  have hhqR' : (h : ℝ) ≤ 4 * q + 3 := by exact_mod_cast hhq'
  have hER : (16 : ℝ) ≤ E.card := by exact_mod_cast hE
  have hprod : (h : ℝ) * ((k - 1 : ℕ) : ℝ) ≤
      (4 * (q : ℝ) + 3) * ((q : ℝ) - 1) := by
    exact mul_le_mul hhqR' hkpredCast (by positivity) (by positivity)
  have hcoef : (0 : ℝ) <
      (3 * (q : ℝ) + 2) ^ 2 - 2 * (h : ℝ) * (k - 1 : ℕ) := by
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith [sq_nonneg (q : ℝ)]
  have hlow := mul_le_mul_of_nonneg_right hER hcoef.le
  have hprodZ : (h : ℝ) * (3 * (q : ℝ) + 2) ≤
      (4 * (q : ℝ) + 3) * (3 * (q : ℝ) + 2) := by
    exact mul_le_mul_of_nonneg_right hhqR' (by positivity)
  have hJ' :
      (E.card : ℝ) *
          ((3 * (q : ℝ) + 2) ^ 2 -
            2 * (h : ℝ) * ((k - 1 : ℕ) : ℝ)) ≤
        2 * (h : ℝ) *
          (3 * (q : ℝ) + 2 - ((k - 1 : ℕ) : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow]
      using hJ
  nlinarith

/-- Residue-uniform ultra-core Johnson bound.  The worst residue estimates
are already strict once `floor(h / 16) >= 26`, hence `h >= 416`. -/
theorem ultra_core_family_card_le_three_generic
    {U Line : Type*} [Fintype U] [DecidableEq U] [DecidableEq Line]
    (h k : ℕ) (hh : 416 ≤ h) (hk : 1 ≤ k) (hrate : 4 * k ≤ h)
    (hU : Fintype.card U = 2 * h)
    (Q : Finset Line) (core : Line → Finset U)
    (hsize : ∀ line ∈ Q, 15 * (h / 16) + 1 ≤ (core line).card)
    (hinter : ∀ line ∈ Q, ∀ line' ∈ Q, line ≠ line' →
      (core line ∩ core line').card ≤ k - 1) :
    Q.card ≤ 3 := by
  let q := h / 16
  have hq : 26 ≤ q := by
    dsimp only [q]
    omega
  have hhq' : h ≤ 16 * q + 15 := by
    dsimp only [q]
    omega
  have hkq : k ≤ 4 * q + 3 := by omega
  have hdZ : k - 1 ≤ 15 * q + 1 := by omega
  have hJ := johnson_core_packing
    Q core (15 * q + 1) (k - 1) hdZ
      (by simpa only [q] using hsize) hinter
  rw [hU] at hJ
  by_contra hnot
  have hQ : 4 ≤ Q.card := by omega
  have hqR : (26 : ℝ) ≤ q := by exact_mod_cast hq
  have hhqR' : (h : ℝ) ≤ 16 * q + 15 := by exact_mod_cast hhq'
  have hkqR : ((k - 1 : ℕ) : ℝ) ≤ 4 * q + 2 := by
    rw [Nat.cast_sub hk, Nat.cast_one]
    have hkqR' : (k : ℝ) ≤ 4 * q + 3 := by exact_mod_cast hkq
    linarith
  have hQR : (4 : ℝ) ≤ Q.card := by exact_mod_cast hQ
  have hprod : (h : ℝ) * ((k - 1 : ℕ) : ℝ) ≤
      (16 * (q : ℝ) + 15) * (4 * (q : ℝ) + 2) := by
    exact mul_le_mul hhqR' hkqR (by positivity) (by positivity)
  have hcoef : (0 : ℝ) <
      (15 * (q : ℝ) + 1) ^ 2 - 2 * (h : ℝ) * (k - 1 : ℕ) := by
    nlinarith [sq_nonneg ((q : ℝ) - 2)]
  have hlow := mul_le_mul_of_nonneg_right hQR hcoef.le
  have hprodZ : (h : ℝ) * (15 * (q : ℝ) + 1) ≤
      (16 * (q : ℝ) + 15) * (15 * (q : ℝ) + 1) := by
    exact mul_le_mul_of_nonneg_right hhqR' (by positivity)
  have hJ' :
      (Q.card : ℝ) *
          ((15 * (q : ℝ) + 1) ^ 2 -
            2 * (h : ℝ) * ((k - 1 : ℕ) : ℝ)) ≤
        2 * (h : ℝ) *
          (15 * (q : ℝ) + 1 - ((k - 1 : ℕ) : ℝ)) := by
    convert hJ using 1 <;> push_cast <;> ring
  nlinarith [sq_nonneg ((q : ℝ) - 26)]

/-- Both Johnson strata needed by the canonical pruning proof hold at its
intrinsic union-budget cutoff `h >= 1699`. -/
theorem johnson_strata_at_union_cutoff
    {U Line : Type*} [Fintype U] [DecidableEq U] [DecidableEq Line]
    (h k : ℕ) (hh : 1699 ≤ h) (hk : 1 ≤ k) (hrate : 4 * k ≤ h)
    (hU : Fintype.card U = 2 * h)
    (E Q : Finset Line) (core : Line → Finset U) (hQE : Q ⊆ E)
    (hEsize : ∀ line ∈ E, 3 * (h / 4) + 2 ≤ (core line).card)
    (hQsize : ∀ line ∈ Q, 15 * (h / 16) + 1 ≤ (core line).card)
    (hinter : ∀ line ∈ E, ∀ line' ∈ E, line ≠ line' →
      (core line ∩ core line').card ≤ k - 1) :
    E.card ≤ 15 ∧ Q.card ≤ 3 := by
  refine ⟨exceptional_core_family_card_le_fifteen_generic
    h k hk hrate hU E core hEsize hinter, ?_⟩
  apply ultra_core_family_card_le_three_generic
    h k (by omega) hk hrate hU Q core hQsize
  intro line hline line' hline' hne
  exact hinter line (hQE hline) line' (hQE hline') hne

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthCutoffArithmetic

#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthCutoffArithmetic.seven_mul_le_five_mul_of_union_envelope
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthCutoffArithmetic.union_envelope_cutoff_sharp
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthCutoffArithmetic.exceptional_core_family_card_le_fifteen_generic
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthCutoffArithmetic.ultra_core_family_card_le_three_generic
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthCutoffArithmetic.johnson_strata_at_union_cutoff
