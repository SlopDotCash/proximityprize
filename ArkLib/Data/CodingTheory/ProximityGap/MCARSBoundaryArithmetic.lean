/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAStaircaseRS
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound

/-!
# Round 5 (#357): the RS boundary row is ARITHMETIC — the curve-point refutation at `d = 2b−1`

The strip-cell programme (issue record, 2026-06-11) located the exact Reed–Solomon
staircase threshold at `d = 2b` and predicted failure at `d = 2b − 1` governed by the
`F_q`-points of a determinant curve. This file formalizes the witness: for
`RS[F₁₀₁, (1,…,8), k = 4]` (distance `5 = 2b − 1` at band `b = 3`), the stack

  `u₀ = (64,10,0,…,0)`, `u₁ = (37,91,23,70,0,…,0)`

has **four** bad scalars `γ ∈ {0, 1, 2, 33}` at `δ = 1/4` (band 3: `δ·n = 2 < 3`) — the
γ-tuple is a rational point of the determinant quadric
`Q(g,h) = g²h²+294g²h+105g²−296gh²−504gh+400h²`. Each event's no-explanation clause is
killed through the second row: any explaining codeword agrees with `u₁` at four domain
points, is therefore the explicit interpolant (degree `< 4` root counting), and the
interpolant provably misses `u₁` at a fifth witness point.

* `mcaEvent_g0/g1/g2/g33` — the four events;
* `rs_band3_fails_at_dist5` — four bad scalars: the band-3 collapse (`≤ 3`) **fails** for
  RS at `d = 2b − 1`, while the cell sweep certifies it at `d = 2b`;
* `epsMCA_rs_boundary_ge` — quantitatively: `ε_mca ≥ 4/101` exceeds the staircase value
  `(⌊δn⌋+1)/q = 3/101` at the boundary row.

**Significance.** Together with the `d ≥ 2b` collapse data this pins the MDS threshold
exactly, and exhibits the first machine-checked instance of ε_mca depending on the
*arithmetic* of the evaluation domain (the curve's rational points) rather than on
`(n, k, q, δ)` alone — the finite-scale prototype of the prize window's conjectured
root-of-unity barrier defining δ*.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code Polynomial

namespace ProximityGap.MCARSBoundaryArithmetic

abbrev F101 := ZMod 101

instance primeFact_MCARSBoundaryArithmetic_1 : Fact (Nat.Prime 101) := ⟨by decide⟩

/-- The evaluation domain `(1, …, 8)`. -/
def dom : Fin 8 ↪ F101 :=
  ⟨fun i => (![1, 2, 3, 4, 5, 6, 7, 8] : Fin 8 → F101) i, by decide⟩

/-- `RS[F₁₀₁, (1,…,8), 4]` — length 8, dimension 4, distance 5. -/
noncomputable def rsC : Submodule F101 (Fin 8 → F101) := ReedSolomon.code dom 4

def u0 : Fin 8 → F101 := ![64, 10, 0, 0, 0, 0, 0, 0]

def u1 : Fin 8 → F101 := ![37, 91, 23, 70, 0, 0, 0, 0]

/-- Explicit cubic. -/
noncomputable def cubic (c0 c1 c2 c3 : F101) : F101[X] :=
  C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3

theorem cubic_eval (c0 c1 c2 c3 x : F101) :
    (cubic c0 c1 c2 c3).eval x = c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3 := by
  simp [cubic]

theorem cubic_mem (c0 c1 c2 c3 : F101) : cubic c0 c1 c2 c3 ∈ degreeLT F101 4 := by
  rw [mem_degreeLT]
  refine lt_of_le_of_lt ?_ (by decide : (3 : WithBot ℕ) < 4)
  unfold cubic
  compute_degree

/-- Membership of an explicit cubic evaluation vector. -/
theorem eval_mem (c0 c1 c2 c3 : F101) :
    (fun j => (cubic c0 c1 c2 c3).eval (dom j)) ∈ rsC :=
  ⟨cubic c0 c1 c2 c3, cubic_mem c0 c1 c2 c3, rfl⟩

/-- **The uniform second-row kill**: any pair explanation on a witness `S` would give a
codeword agreeing with `u₁` on `S`; it then coincides with the explicit interpolant `q` at
the four points of `T ⊆ S` (degree-`< 4` root counting), but `q` provably misses `u₁` at
the fifth witness point `viol ∈ S`. -/
theorem no_explain (S : Finset (Fin 8)) (q0 q1 q2 q3 : F101)
    (T : Finset (Fin 8)) (hTcard : T.card = 4) (hTS : T ⊆ S)
    (hqT : ∀ i ∈ T, (cubic q0 q1 q2 q3).eval (dom i) = u1 i)
    (viol : Fin 8) (hviolS : viol ∈ S)
    (hqviol : (cubic q0 q1 q2 q3).eval (dom viol) ≠ u1 viol) :
    ¬ pairJointAgreesOn (rsC : Set (Fin 8 → F101)) S u0 u1 := by
  rintro ⟨v₀, _, v₁, hv₁, hag⟩
  obtain ⟨p, hp, rfl⟩ := hv₁
  set q : F101[X] := cubic q0 q1 q2 q3 with hq
  -- p − q vanishes at the four points of T
  have hdiff : p - q = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero (v := dom) T
      (Set.injOn_of_injective dom.injective) ?_ ?_
    · rw [hTcard]
      refine lt_of_le_of_lt (degree_sub_le p q) ?_
      rw [max_lt_iff]
      exact ⟨mem_degreeLT.mp hp, mem_degreeLT.mp (cubic_mem q0 q1 q2 q3)⟩
    · intro i hi
      have hagi := (hag i (hTS hi)).2
      have hpi : p.eval (dom i) = u1 i := hagi
      rw [eval_sub, hpi, hqT i hi, sub_self]
  have hpq : p = q := by
    have h := sub_eq_zero.mp hdiff
    exact h
  -- evaluate at the violated point
  have hagv := (hag viol hviolS).2
  have hpv : p.eval (dom viol) = u1 viol := hagv
  rw [hpq] at hpv
  exact hqviol hpv

/-- The witness-size clause at `δ = 1/4`, `n = 8`: six points suffice. -/
theorem card_clause8 {S : Finset (Fin 8)} (hS : S.card = 6) :
    (S.card : ℝ≥0) ≥ ((1 : ℝ≥0) - 1/4) * (Fintype.card (Fin 8) : ℝ≥0) := by
  rw [hS, Fintype.card_fin]
  calc ((1 : ℝ≥0) - 1/4) * (8 : ℕ)
      ≤ (3/4 : ℝ≥0) * (8 : ℕ) := by
        gcongr
        exact tsub_le_iff_right.mpr (by norm_num)
    _ ≤ ((6 : ℕ) : ℝ≥0) := by push_cast; norm_num

/-- The four witness sets (each: the universe minus one disjoint pair). -/
def S0 : Finset (Fin 8) := {2, 3, 4, 5, 6, 7}
def S1 : Finset (Fin 8) := {0, 1, 4, 5, 6, 7}
def S2 : Finset (Fin 8) := {0, 1, 2, 3, 6, 7}
def S3 : Finset (Fin 8) := {0, 1, 2, 3, 4, 5}

open Classical in
/-- Bad scalar `γ = 0`: the line point is supported on block `{0,1}`; witness `S0`. -/
theorem mcaEvent_g0 :
    mcaEvent (F := F101) (rsC : Set (Fin 8 → F101)) (1/4) u0 u1 (0 : F101) := by
  refine ⟨S0, card_clause8 (by decide), ⟨0, rsC.zero_mem, fun j hj => ?_⟩, ?_⟩
  · fin_cases hj <;> decide
  · refine no_explain S0 37 36 22 48 {2, 3, 4, 5} (by decide) (by decide)
      (fun i hi => ?_) 6 (by decide) ?_
    · fin_cases hi <;> (rw [cubic_eval]; decide)
    · rw [cubic_eval]; decide

open Classical in
/-- Bad scalar `γ = 1`: the line point is supported on block `{2,3}`; witness `S1`. -/
theorem mcaEvent_g1 :
    mcaEvent (F := F101) (rsC : Set (Fin 8 → F101)) (1/4) u0 u1 (1 : F101) := by
  refine ⟨S1, card_clause8 (by decide), ⟨0, rsC.zero_mem, fun j hj => ?_⟩, ?_⟩
  · fin_cases hj <;> decide
  · refine no_explain S1 35 75 29 100 {0, 1, 4, 5} (by decide) (by decide)
      (fun i hi => ?_) 6 (by decide) ?_
    · fin_cases hi <;> (rw [cubic_eval]; decide)
    · rw [cubic_eval]; decide

open Classical in
/-- Bad scalar `γ = 2`: on-line codeword `50 + 16X + 66X² + 6X³`; witness `S2`. -/
theorem mcaEvent_g2 :
    mcaEvent (F := F101) (rsC : Set (Fin 8 → F101)) (1/4) u0 u1 (2 : F101) := by
  refine ⟨S2, card_clause8 (by decide),
    ⟨fun j => (cubic 50 16 66 6).eval (dom j), eval_mem 50 16 66 6, fun j hj => ?_⟩, ?_⟩
  · fin_cases hj <;> (simp only [cubic_eval]; decide)
  · refine no_explain S2 28 15 5 90 {0, 1, 2, 3} (by decide) (by decide)
      (fun i hi => ?_) 6 (by decide) ?_
    · fin_cases hi <;> (rw [cubic_eval]; decide)
    · rw [cubic_eval]; decide

open Classical in
/-- Bad scalar `γ = 33`: on-line codeword `9 + 77X + 19X² + 69X³`; witness `S3`. -/
theorem mcaEvent_g33 :
    mcaEvent (F := F101) (rsC : Set (Fin 8 → F101)) (1/4) u0 u1 (33 : F101) := by
  refine ⟨S3, card_clause8 (by decide),
    ⟨fun j => (cubic 9 77 19 69).eval (dom j), eval_mem 9 77 19 69, fun j hj => ?_⟩, ?_⟩
  · fin_cases hj <;> (simp only [cubic_eval]; decide)
  · refine no_explain S3 28 15 5 90 {0, 1, 2, 3} (by decide) (by decide)
      (fun i hi => ?_) 4 (by decide) ?_
    · fin_cases hi <;> (rw [cubic_eval]; decide)
    · rw [cubic_eval]; decide

open Classical in
/-- **The boundary refutation**: four bad scalars at band 3 — the collapse `≤ 3` fails for
Reed–Solomon at `d = 2b − 1 = 5`, sharply complementing the `d ≥ 2b` cell collapse. -/
theorem rs_band3_fails_at_dist5 :
    3 < (Finset.filter (fun γ : F101 => mcaEvent (F := F101)
      (rsC : Set (Fin 8 → F101)) (1/4) u0 u1 γ) Finset.univ).card := by
  have hsub : ({0, 1, 2, 33} : Finset F101) ⊆ Finset.filter (fun γ : F101 =>
      mcaEvent (F := F101) (rsC : Set (Fin 8 → F101)) (1/4) u0 u1 γ) Finset.univ := by
    intro γ hγ
    fin_cases hγ
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mcaEvent_g0⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mcaEvent_g1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mcaEvent_g2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mcaEvent_g33⟩
  calc 3 < ({0, 1, 2, 33} : Finset F101).card := by decide
    _ ≤ _ := Finset.card_le_card hsub

open Classical in
/-- **Quantitative form**: `ε_mca ≥ 4/101` at the boundary row — strictly above the
staircase value `(⌊δn⌋+1)/q = 3/101`. The excess is governed by the rational points of the
determinant curve: the first machine-checked arithmetic dependence of the MCA error. -/
theorem epsMCA_rs_boundary_ge :
    (4 : ℝ≥0∞) / 101 ≤ epsMCA (F := F101) (A := F101) (rsC : Set (Fin 8 → F101)) (1/4) := by
  refine le_trans ?_ (mcaEvent_prob_le_epsMCA (F := F101) (A := F101)
    (rsC : Set (Fin 8 → F101)) (1/4) ![u0, u1])
  have h0 : (![u0, u1] : WordStack F101 (Fin 2) (Fin 8)) 0 = u0 := rfl
  have h1 : (![u0, u1] : WordStack F101 (Fin 2) (Fin 8)) 1 = u1 := rfl
  rw [h0, h1, prob_uniform_eq_card_filter_div_card]
  have hcard : Fintype.card F101 = 101 := by decide
  rw [hcard]
  have h4 : (4 : ℕ) ≤ (Finset.filter (fun γ : F101 => mcaEvent (F := F101)
      (rsC : Set (Fin 8 → F101)) (1/4) u0 u1 γ) Finset.univ).card :=
    rs_band3_fails_at_dist5
  simp only [ENNReal.coe_natCast]
  gcongr
  · exact_mod_cast h4
  · norm_num

/-! ## Source audit -/

#print axioms no_explain
#print axioms rs_band3_fails_at_dist5
#print axioms epsMCA_rs_boundary_ge

end ProximityGap.MCARSBoundaryArithmetic
