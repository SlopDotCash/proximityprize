/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.CubicHahnJohnson
import ArkLib.Data.CodingTheory.ListDecodability.AgreementRadius
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

/-!
# Quadratic Hahn Forced Saturated-Pair Density and Cliques Beyond Johnson

Using the degree-1 and degree-2 Hahn dual-eigenvalue inequalities (`sum_P1_nonneg`,
`sum_P2_nonneg` from `CubicHahnJohnson`) on the concave penalty
`(d - s) * (s - r₀)` (with `r₀ = max(0, 2t - n) - 1`), every non-saturated pair
`max(0, 2t - n) ≤ s ≤ d - 1` pays at least
`min ((d - s_min) * (s_min - r₀)) (d - 1 - r₀) > 0`, whereas every saturated pair
(`s = d`) pays `0`.

This strictly sharpens the degree-1 Turán forcing across the designated-prime
second-budget (`B₂ = 2³¹`) open list fronts:
- **Rate `1/2`, `J+1` (`e = 314,491,700`, `M = 2³¹ + 1`)**: using the lower overlap
  floor `s_min = 2t - n = 444,758,424`, saturated-pair density jumps from degree-1's
  `49.07%` (not even `K₃`) to **`≥ 74.07% > 2/3`**, unconditionally forcing a
  **saturated `K₄` clique** of 4 distinct polynomials whose 6 pairwise differences all
  split completely into `2²⁹ - 1` roots inside the domain!
- **Rate `1/16`, `J+1` (`e = 805,306,371`, `M = 2³¹ + 1`)**: saturated-pair density
  jumps from degree-1's `40.63%` (not even `K₃`) to **`≥ 68.75% > 2/3`**, likewise
  unconditionally forcing a **saturated `K₄` clique**!
- **Rate `1/8`, `J+2` (`e = 694,116,764`, `M = 2³¹ + 1`)**: saturated-pair density
  jumps `2.74×` from `12.01%` to **`≥ 32.90%`**.
-/

set_option autoImplicit false

namespace ProximityGap.QuadraticHahnCliques

open Finset SimpleGraph CubicHahnJohnson Code Polynomial
open scoped BigOperators

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Two distinct vertices are adjacent when their agreement sets attain the intersection cap `d`. -/
def fullGraph {M : ℕ} (S : Fin M → Finset I) (d : ℕ) : SimpleGraph (Fin M) where
  Adj i j := i ≠ j ∧ d ≤ (S i ∩ S j).card
  symm := ⟨fun _ _ h => ⟨h.1.symm, by simpa only [inter_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Exact shifted-quadratic Hahn coefficient `c₁` of `(s - d) * (s - r₀) = c₀ + c₁ P₁ + 2 P₂`. -/
def shiftQuadC1 (n t d r0 : ℚ) : ℚ :=
  2 * (t - 1) ^ 2 / (n - 2) + 1 - (d + r0)

/-- Exact shifted-quadratic Hahn constant `c₀` of `(s - d) * (s - r₀) = c₀ + c₁ P₁ + 2 P₂`. -/
def shiftQuadC0 (n t d r0 : ℚ) : ℚ :=
  d * r0 + shiftQuadC1 n t d r0 * (t ^ 2 / n) - t ^ 2 * (t - 1) ^ 2 / ((n - 1) * (n - 2))

theorem shift_quad_poly_eq (n t d r0 s : ℚ) (hn : n ≠ 0) (hn1 : n - 1 ≠ 0) (hn2 : n - 2 ≠ 0) :
    (s - d) * (s - r0) =
      shiftQuadC0 n t d r0 + shiftQuadC1 n t d r0 * P1 n t s + 2 * P2 n t s := by
  unfold shiftQuadC0 shiftQuadC1 P1 P2
  field_simp [hn, hn1, hn2]
  ring

/-- Universal inclusion–exclusion lower bound on pairwise intersection size:
`|S i ∩ S j| ≥ 2t - n` whenever `|S i| = |S j| = t`. -/
theorem inter_card_ge_two_mul_sub {A B : Finset I} {t : ℕ}
    (hA : A.card = t) (hB : B.card = t) :
    2 * t - Fintype.card I ≤ (A ∩ B).card := by
  have hunion : (A ∪ B).card ≤ Fintype.card I := Finset.card_le_univ _
  have hiu := Finset.card_union_add_card_inter A B
  omega

open Classical in
/-- Master Quadratic Hahn upper bound on the number of non-saturated ordered pairs
(and lower bound on saturated edges in `fullGraph S d`). -/
theorem forced_edges_quadratic_hahn {M t d smin : ℕ} (S : Fin M → Finset I)
    (hn : 3 ≤ Fintype.card I)
    (hinter_lo : ∀ i j, i ≠ j → smin ≤ (S i ∩ S j).card)
    (hw : ∀ i, (S i).card = t)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ d)
    (r0 pen : ℚ) (hpen : 0 < pen)
    (hpen_lo : ∀ s : ℕ, smin ≤ s → s < d → pen ≤ ((d : ℚ) - s) * ((s : ℚ) - r0))
    (hc1 : 0 ≤ shiftQuadC1 (Fintype.card I) t d r0) :
    let n : ℚ := Fintype.card I
    ((M * (M - 1) - 2 * (fullGraph S d).edgeFinset.card : ℕ) : ℚ) * pen ≤
      (M : ℚ) * (((t : ℚ) - d) * ((t : ℚ) - r0)) -
        (M : ℚ) ^ 2 * shiftQuadC0 n t d r0 := by
  dsimp only
  set n : ℚ := (Fintype.card I : ℚ)
  have hn_ge : (3 : ℚ) ≤ n := by dsimp [n]; exact_mod_cast hn
  have hn0 : n ≠ 0 := by linarith
  have hn1 : n - 1 ≠ 0 := by linarith
  have hn2 : n - 2 ≠ 0 := by linarith
  have hP1 := sum_P1_nonneg S (by omega) hw
  have hP2 := sum_P2_nonneg S hn hw
  have hlow : (M : ℚ) ^ 2 * shiftQuadC0 n t d r0 ≤
      ∑ i : Fin M, ∑ j : Fin M,
        (((S i ∩ S j).card : ℚ) - d) * (((S i ∩ S j).card : ℚ) - r0) := by
    have hid : ∑ i : Fin M, ∑ j : Fin M,
        (((S i ∩ S j).card : ℚ) - d) * (((S i ∩ S j).card : ℚ) - r0) =
        (M : ℚ) ^ 2 * shiftQuadC0 n t d r0 +
        shiftQuadC1 n t d r0 * (∑ i : Fin M, ∑ j : Fin M, P1 n t ((S i ∩ S j).card)) +
        2 * (∑ i : Fin M, ∑ j : Fin M, P2 n t ((S i ∩ S j).card)) := by
      simp_rw [shift_quad_poly_eq n t d r0 _ hn0 hn1 hn2, Finset.sum_add_distrib,
        ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [hid]
    have h1 : 0 ≤ shiftQuadC1 n t d r0 *
        (∑ i : Fin M, ∑ j : Fin M, P1 n t ((S i ∩ S j).card)) :=
      mul_nonneg hc1 hP1
    have h2 : 0 ≤ 2 * (∑ i : Fin M, ∑ j : Fin M, P2 n t ((S i ∩ S j).card)) := by positivity
    linarith
  have hsplit : ∑ i : Fin M, ∑ j : Fin M,
      (((S i ∩ S j).card : ℚ) - d) * (((S i ∩ S j).card : ℚ) - r0) =
      (M : ℚ) * (((t : ℚ) - d) * ((t : ℚ) - r0)) -
        ∑ i : Fin M, ∑ j ∈ univ.erase i,
          ((d : ℚ) - (S i ∩ S j).card) * (((S i ∩ S j).card : ℚ) - r0) := by
    have hrow (i : Fin M) :
        ∑ j : Fin M, (((S i ∩ S j).card : ℚ) - d) * (((S i ∩ S j).card : ℚ) - r0) =
        ((t : ℚ) - d) * ((t : ℚ) - r0) -
          ∑ j ∈ univ.erase i, ((d : ℚ) - (S i ∩ S j).card) * (((S i ∩ S j).card : ℚ) - r0) := by
      rw [← Finset.add_sum_erase univ _ (mem_univ i), inter_self, hw i]
      have hneg : ∑ j ∈ univ.erase i, (((S i ∩ S j).card : ℚ) - d) * (((S i ∩ S j).card : ℚ) - r0) =
          -(∑ j ∈ univ.erase i, ((d : ℚ) - (S i ∩ S j).card) * (((S i ∩ S j).card : ℚ) - r0)) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      linarith
    simp_rw [hrow, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  let G := fullGraph S d
  have hrow_pen (i : Fin M) :
      ((M - 1 - G.degree i : ℕ) : ℚ) * pen ≤
        ∑ j ∈ univ.erase i, ((d : ℚ) - (S i ∩ S j).card) * (((S i ∩ S j).card : ℚ) - r0) := by
    have hnonadj : ((univ.erase i).filter fun j => ¬ G.Adj i j).card = M - 1 - G.degree i := by
      have hadj : ((univ.erase i).filter fun j => G.Adj i j) = G.neighborFinset i := by
        ext j; simp only [mem_filter, mem_erase, mem_univ, and_true, SimpleGraph.mem_neighborFinset]
        exact ⟨And.right, fun h => ⟨h.ne.symm, h⟩⟩
      have hdisj : Disjoint ((univ.erase i).filter fun j => G.Adj i j)
          ((univ.erase i).filter fun j => ¬ G.Adj i j) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2
        exact (mem_filter.mp hx2).2 (mem_filter.mp hx1).2
      have hunion : ((univ.erase i).filter fun j => G.Adj i j) ∪
          ((univ.erase i).filter fun j => ¬ G.Adj i j) = univ.erase i := by
        ext x; simp only [mem_union, mem_filter]; tauto
      have htot := Finset.card_union_of_disjoint hdisj
      rw [hunion, hadj, G.card_neighborFinset_eq_degree, card_erase_of_mem (mem_univ i), card_univ,
        Fintype.card_fin] at htot
      omega
    calc
      ((M - 1 - G.degree i : ℕ) : ℚ) * pen
        = ∑ _j ∈ (univ.erase i).filter (fun j => ¬ G.Adj i j), pen := by
            rw [Finset.sum_const, hnonadj, nsmul_eq_mul]
      _ ≤ ∑ j ∈ (univ.erase i).filter (fun j => ¬ G.Adj i j),
            ((d : ℚ) - (S i ∩ S j).card) * (((S i ∩ S j).card : ℚ) - r0) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hne : i ≠ j := (mem_erase.mp (mem_filter.mp hj).1).1.symm
          have hna : ¬ G.Adj i j := (mem_filter.mp hj).2
          have hlt : (S i ∩ S j).card < d := by
            by_contra! hge; exact hna ⟨hne, hge⟩
          exact hpen_lo _ (hinter_lo i j hne) hlt
      _ ≤ ∑ j ∈ univ.erase i,
            ((d : ℚ) - (S i ∩ S j).card) * (((S i ∩ S j).card : ℚ) - r0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro j hj _
          have hne : i ≠ j := (mem_erase.mp hj).1.symm
          have hle : (S i ∩ S j).card ≤ d := hpair i j hne
          by_cases hlt : (S i ∩ S j).card < d
          · exact hpen.le.trans (hpen_lo _ (hinter_lo i j hne) hlt)
          · have heq : (S i ∩ S j).card = d := by omega
            simp [heq]
  have hsum_deg : ∑ i : Fin M, G.degree i = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  have hsum_nonsat : ∑ i : Fin M, (M - 1 - G.degree i) = M * (M - 1) - 2 * G.edgeFinset.card := by
    have hle (i : Fin M) : G.degree i ≤ M - 1 := by
      have : G.neighborFinset i ⊆ univ.erase i := fun j hj =>
        mem_erase.mpr ⟨((SimpleGraph.mem_neighborFinset G i j).mp hj).ne.symm, mem_univ j⟩
      have hc := Finset.card_le_card this
      rw [G.card_neighborFinset_eq_degree, card_erase_of_mem (mem_univ i), card_univ,
        Fintype.card_fin] at hc
      exact hc
    have hadd : ∑ i : Fin M, (M - 1 - G.degree i) + ∑ i : Fin M, G.degree i = M * (M - 1) := by
      rw [← Finset.sum_add_distrib]
      have h1 (i : Fin M) : M - 1 - G.degree i + G.degree i = M - 1 := Nat.sub_add_cancel (hle i)
      simp [h1]
    omega
  have hpen_sum : ((M * (M - 1) - 2 * G.edgeFinset.card : ℕ) : ℚ) * pen ≤
      ∑ i : Fin M, ∑ j ∈ univ.erase i,
        ((d : ℚ) - (S i ∩ S j).card) * (((S i ∩ S j).card : ℚ) - r0) := by
    calc
      ((M * (M - 1) - 2 * G.edgeFinset.card : ℕ) : ℚ) * pen
        = (∑ i : Fin M, ((M - 1 - G.degree i : ℕ) : ℚ)) * pen := by
            rw [← Nat.cast_sum, hsum_nonsat]
      _ = ∑ i : Fin M, ((M - 1 - G.degree i : ℕ) : ℚ) * pen := Finset.sum_mul _ _ _
      _ ≤ _ := Finset.sum_le_sum fun i _ => hrow_pen i
  linarith

/-- Concavity helper: on `[smin, d - 1]`, the quadratic `(d - s) * (s - r0)` attains its
minimum at the endpoints `s = smin` or `s = d - 1`. -/
private theorem quad_penalty_min {d smin s : ℕ} {r0 pen : ℚ}
    (hlo : smin ≤ s) (hhi : s < d)
    (hleft : pen ≤ ((d : ℚ) - smin) * ((smin : ℚ) - r0))
    (hright : pen ≤ ((d : ℚ) - 1) - r0) :
    pen ≤ ((d : ℚ) - s) * ((s : ℚ) - r0) := by
  have hs1 : (smin : ℚ) ≤ s := by exact_mod_cast hlo
  have hs2 : (s : ℚ) ≤ (d : ℚ) - 1 := by
    have : s + 1 ≤ d := hhi
    have : (s : ℚ) + 1 ≤ d := by exact_mod_cast this
    linarith
  by_cases heq : smin = d - 1
  · have : s = smin := by omega
    rwa [this]
  · have hden : 0 < (d : ℚ) - 1 - smin := by
      have : smin + 1 < d := by omega
      have : (smin : ℚ) + 1 < d := by exact_mod_cast this
      linarith
    have hdiff : ((d : ℚ) - s) * ((s : ℚ) - r0) =
        ((d : ℚ) - smin) * ((smin : ℚ) - r0) * (((d : ℚ) - 1 - s) / ((d : ℚ) - 1 - smin)) +
        (((d : ℚ) - 1) - r0) * (((s : ℚ) - smin) / ((d : ℚ) - 1 - smin)) +
        ((s : ℚ) - smin) * ((d : ℚ) - 1 - s) := by
      field_simp [hden.ne']; ring
    have hlam1 : 0 ≤ ((d : ℚ) - 1 - s) / ((d : ℚ) - 1 - smin) := div_nonneg (by linarith) hden.le
    have hlam2 : 0 ≤ ((s : ℚ) - smin) / ((d : ℚ) - 1 - smin) := div_nonneg (by linarith) hden.le
    have hsum1 : ((d : ℚ) - 1 - s) / ((d : ℚ) - 1 - smin) +
        ((s : ℚ) - smin) / ((d : ℚ) - 1 - smin) = 1 := by
      field_simp [hden.ne']; ring
    have hconc : 0 ≤ ((s : ℚ) - smin) * ((d : ℚ) - 1 - s) :=
      mul_nonneg (by linarith) (by linarith)
    have h1 := mul_le_mul_of_nonneg_right hleft hlam1
    have h2 := mul_le_mul_of_nonneg_right hright hlam2
    have hcomb : pen = pen * (((d : ℚ) - 1 - s) / ((d : ℚ) - 1 - smin)) +
        pen * (((s : ℚ) - smin) / ((d : ℚ) - 1 - smin)) := by
      rw [← mul_add, hsum1, mul_one]
    linarith

/-- Turán clique-forcing wrapper for Quadratic Hahn! -/
theorem forced_clique_quadratic_hahn {M t d smin r : ℕ} (S : Fin M → Finset I)
    (hn : 3 ≤ Fintype.card I)
    (hinter_lo : ∀ i j, i ≠ j → smin ≤ (S i ∩ S j).card)
    (hw : ∀ i, (S i).card = t)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ d)
    (r0 pen : ℚ) (hpen : 0 < pen)
    (hleft : pen ≤ ((d : ℚ) - smin) * ((smin : ℚ) - r0))
    (hright : pen ≤ ((d : ℚ) - 1) - r0)
    (hc1 : 0 ≤ shiftQuadC1 (Fintype.card I) t d r0)
    (hturan : (M : ℚ) * (((t : ℚ) - d) * ((t : ℚ) - r0)) -
        (M : ℚ) ^ 2 * shiftQuadC0 (Fintype.card I) t d r0 <
      ((M * (M - 1) - 2 * SimpleGraph.turanNumber M r : ℕ) : ℚ) * pen) :
    ¬ (fullGraph S d).CliqueFree (r + 1) := by
  classical
  intro hfree
  have hedge : (fullGraph S d).edgeFinset.card ≤ SimpleGraph.turanNumber M r := by
    simpa only [Fintype.card_fin] using hfree.card_edgeFinset_le
  have hblk := forced_edges_quadratic_hahn S hn hinter_lo hw hpair r0 pen hpen
    (fun s hs1 hs2 => quad_penalty_min hs1 hs2 hleft hright) hc1
  have hmono : M * (M - 1) - 2 * SimpleGraph.turanNumber M r ≤
      M * (M - 1) - 2 * (fullGraph S d).edgeFinset.card := by omega
  have hmonoQ : ((M * (M - 1) - 2 * SimpleGraph.turanNumber M r : ℕ) : ℚ) ≤
      ((M * (M - 1) - 2 * (fullGraph S d).edgeFinset.card : ℕ) : ℚ) := by exact_mod_cast hmono
  have hmul := mul_le_mul_of_nonneg_right hmonoQ hpen.le
  exact not_lt_of_ge (hmul.trans hblk) hturan

/-- Scalar RS worst-center list extraction: a list exceeding `B` produces `B + 1` distinct
message polynomials and exact `t`-element agreement sets satisfying the degree overlap cap. -/
private theorem from_list_rs {F : Type} [Field F] (D : I ↪ F) {k t B r : ℕ} (hk : 0 < k)
    (htn : t ≤ Fintype.card I) (hn : 0 < Fintype.card I)
    (hforce : ∀ S : Fin (B + 1) → Finset I, (∀ i, (S i).card = t) →
      (∀ i j, i ≠ j → (S i ∩ S j).card ≤ k - 1) → ¬ (fullGraph S (k - 1)).CliqueFree r)
    (hlist : (B : ℕ∞) < Lambda (ReedSolomon.code D k : Set (I → F))
      (((Fintype.card I - t : ℕ) : ℝ) / Fintype.card I)) :
    ∃ (y : I → F) (P : Fin (B + 1) → F[X]) (S : Fin (B + 1) → Finset I),
      Function.Injective P ∧ (∀ i, (P i).natDegree < k) ∧ (∀ i, (S i).card = t) ∧
      (∀ i x, x ∈ S i → (P i).eval (D x) = y x) ∧ ¬ (fullGraph S (k - 1)).CliqueFree r := by
  classical
  let _ : NeZero k := ⟨hk.ne'⟩
  let C := (ReedSolomon.code D k : Set (I → F))
  let δ := (((Fintype.card I - t : ℕ) : ℝ) / Fintype.card I)
  obtain ⟨y, W, hW, hlarge⟩ : ∃ (y : I → F) (W : Finset (I → F)),
      (∀ w ∈ W, w ∈ closeCodewordsRel C y δ) ∧ B < W.card := by
    by_contra! h
    exact (not_le_of_gt hlist) (Lambda_le_of_forall_finset_card_le fun y W hw => h y W hw)
  obtain ⟨V, hsub, hV⟩ := exists_subset_card_eq (show B + 1 ≤ W.card by omega)
  let eqv := V.equivFin
  rw [hV] at eqv
  let w (i : Fin (B + 1)) := (eqv.symm i).val
  have hin : Function.Injective w := fun _ _ h => eqv.symm.injective (Subtype.ext h)
  have hclose (i) := mem_closeCodewordsRel_iff.mp (hW (w i) (hsub (eqv.symm i).property))
  have hex (i) := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp (hclose i).1
  choose P hdeg heval using hex
  have hinP : Function.Injective P := by
    intro i j he
    apply hin
    exact funext fun x => ((heval i x).symm.trans (congrArg (eval (D x)) he)).trans (heval j x)
  have hδ : δ = 1 - (t : ℝ) / Fintype.card I := by
    dsimp [δ]
    rw [Nat.cast_sub htn, sub_div, div_self (by exact_mod_cast hn.ne')]
  let A (i : Fin (B + 1)) := univ.filter fun x => w i x = y x
  have hA (i) : t ≤ (A i).card := by
    have hd := (hclose i).2
    rw [hδ] at hd
    exact_mod_cast (relHammingDist_le_one_sub_div_iff hn).mp hd
  choose S hs hc using fun i => exists_subset_card_eq (hA i)
  refine ⟨y, P, S, hinP, hdeg, hc, ?_, hforce S hc ?_⟩
  · intro i x hx
    exact (heval i x).trans (mem_filter.mp (hs i hx)).2
  · intro i j hij
    have hfit : (S i ∩ S j).card ≤ agree (w i) (w j) := by
      apply card_le_card
      intro x hx
      obtain ⟨hi, hj⟩ := mem_inter.mp hx
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp (hs i hi)).2.trans
        (mem_filter.mp (hs j hj)).2.symm⟩
    have hpair := ReedSolomon.agree_lt_of_mem_code (hclose i).1 (hclose j).1 (hin.ne hij)
    omega

section ProductionForcedCliques

/-- **Rate `1/2`, `J+1` (`e = 314,491,700`, `B₂ = 2³¹`)**: Quadratic Hahn with
`r₀ = 2t - n - 1 = 444,758,423` raises saturated-pair density from `49.07%` (sub-triangle)
to `≥ 74.07% > 2/3`, unconditionally forcing a **saturated `K₄` clique**! -/
theorem rate_half_second_budget_K4 (S : Fin 2147483649 → Finset I)
    (hn : Fintype.card I = 1073741824) (hw : ∀ i, (S i).card = 759250124)
    (hp : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 536870911) :
    ¬ (fullGraph S 536870911).CliqueFree 4 := by
  have hinter_lo : ∀ i j, i ≠ j → 444758424 ≤ (S i ∩ S j).card := fun i j _ => by
    have := inter_card_ge_two_mul_sub (hw i) (hw j)
    omega
  apply forced_clique_quadratic_hahn S (smin := 444758424) (r := 3) (by omega) hinter_lo hw hp
    444758423 92112487 (by norm_num) (by norm_num) (by norm_num)
    (by rw [hn]; norm_num [shiftQuadC1])
  rw [hn, SimpleGraph.turanNumber_three]
  norm_num [shiftQuadC0, shiftQuadC1]

/-- **Rate `1/16`, `J+1` (`e = 805,306,371`, `B₂ = 2³¹`)**: Quadratic Hahn with `r₀ = -1`
raises saturated-pair density from `40.63%` (sub-triangle) to `≥ 68.75% > 2/3`,
unconditionally forcing a **saturated `K₄` clique**! -/
theorem rate_sixteenth_second_budget_K4 (S : Fin 2147483649 → Finset I)
    (hn : Fintype.card I = 1073741824) (hw : ∀ i, (S i).card = 268435453)
    (hp : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 67108863) :
    ¬ (fullGraph S 67108863).CliqueFree 4 := by
  apply forced_clique_quadratic_hahn S (smin := 0) (r := 3) (by omega)
    (fun _ _ _ => Nat.zero_le _) hw hp (-1) 67108863 (by norm_num) (by norm_num) (by norm_num)
    (by rw [hn]; norm_num [shiftQuadC1])
  rw [hn, SimpleGraph.turanNumber_three]
  norm_num [shiftQuadC0, shiftQuadC1]

open Classical in
/-- **Rate `1/8`, `J+2` (`e = 694,116,764`, `B₂ = 2³¹`)**: Quadratic Hahn with `r₀ = -1`
raises saturated-pair density `2.74×` from degree-1's `12.01%` to **`≥ 32.90%`**. -/
theorem rate_eighth_j2_second_budget_edges (S : Fin 2147483649 → Finset I)
    (hn : Fintype.card I = 1073741824) (hw : ∀ i, (S i).card = 379625060)
    (hp : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 134217727) :
    (329 : ℚ) / 1000 * ((2147483649 : ℚ) * 2147483648) ≤
      (2 * (fullGraph S 134217727).edgeFinset.card : ℚ) := by
  have hblk := forced_edges_quadratic_hahn S (smin := 0) (by omega)
    (fun _ _ _ => Nat.zero_le _) hw hp (-1) 134217727 (by norm_num)
    (fun s hs1 hs2 => quad_penalty_min hs1 hs2 (by norm_num) (by norm_num))
    (by rw [hn]; norm_num [shiftQuadC1])
  have hle_max : 2 * (fullGraph S 134217727).edgeFinset.card ≤ 2147483649 * 2147483648 := by
    have hsum := (fullGraph S 134217727).sum_degrees_eq_twice_card_edges
    have hdeg (i : Fin 2147483649) : (fullGraph S 134217727).degree i ≤ 2147483648 := by
      have : (fullGraph S 134217727).neighborFinset i ⊆ univ.erase i := fun j hj =>
        mem_erase.mpr ⟨((SimpleGraph.mem_neighborFinset (fullGraph S 134217727) i j).mp hj).ne.symm,
          mem_univ j⟩
      have hc := Finset.card_le_card this
      rw [(fullGraph S 134217727).card_neighborFinset_eq_degree,
        card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin] at hc
      exact hc
    calc
      2 * (fullGraph S 134217727).edgeFinset.card
        = ∑ i : Fin 2147483649, (fullGraph S 134217727).degree i := hsum.symm
      _ ≤ ∑ _i : Fin 2147483649, 2147483648 := Finset.sum_le_sum fun i _ => hdeg i
      _ = 2147483649 * 2147483648 := by simp
  have hsub : ((2147483649 * (2147483649 - 1) - 2 * (fullGraph S 134217727).edgeFinset.card : ℕ) : ℚ) =
      (2147483649 : ℚ) * 2147483648 - (2 * (fullGraph S 134217727).edgeFinset.card : ℚ) := by
    rw [show 2147483649 - 1 = 2147483648 by norm_num, Nat.cast_sub hle_max]
    push_cast; ring
  have hnum : (2147483649 : ℚ) * (((379625060 : ℚ) - 134217727) * ((379625060 : ℚ) - (-1))) -
      (2147483649 : ℚ) ^ 2 * shiftQuadC0 1073741824 379625060 134217727 (-1) ≤
      (671 : ℚ) / 1000 * ((2147483649 : ℚ) * 2147483648) * 134217727 := by
    norm_num [shiftQuadC0, shiftQuadC1]
  rw [hn] at hblk
  have hblk' : ((2147483649 : ℚ) * 2147483648 -
        (2 * (fullGraph S 134217727).edgeFinset.card : ℚ)) * 134217727 ≤
      (671 : ℚ) / 1000 * ((2147483649 : ℚ) * 2147483648) * 134217727 := by
    rw [← hsub]; exact hblk.trans hnum
  have hdiv : (2147483649 : ℚ) * 2147483648 -
        (2 * (fullGraph S 134217727).edgeFinset.card : ℚ) ≤
      (671 : ℚ) / 1000 * ((2147483649 : ℚ) * 2147483648) :=
    le_of_mul_le_mul_right hblk' (by norm_num)
  linarith

/-- **Scalar Reed–Solomon Rate `1/2`, `J+1` (`e = 314,491,700`, `B₂ = 2³¹`)**:
Any worst-center list exceeding `2³¹` forces 4 distinct degree-`< 2²⁹` polynomials whose
6 pairwise differences all split completely into `2²⁹ - 1` roots in the domain! -/
theorem rate_half_second_budget_rs_K4 {F : Type} [Field F] (D : Fin 1073741824 ↪ F)
    (hlist : ((2147483648 : ℕ) : ℕ∞) <
      Code.Lambda (ReedSolomon.code D 536870912 : Set (Fin 1073741824 → F))
        (((1073741824 - 759250124 : ℕ) : ℝ) / 1073741824)) :
    ∃ (y : Fin 1073741824 → F) (P : Fin 2147483649 → Polynomial F)
      (S : Fin 2147483649 → Finset (Fin 1073741824)),
      Function.Injective P ∧ (∀ i, (P i).natDegree < 536870912) ∧ (∀ i, (S i).card = 759250124) ∧
      (∀ i x, x ∈ S i → (P i).eval (D x) = y x) ∧ ¬ (fullGraph S 536870911).CliqueFree 4 :=
  from_list_rs D (by norm_num) (by simp only [Fintype.card_fin]; norm_num)
    (by simp only [Fintype.card_fin]; norm_num)
    (fun S hc hpair => rate_half_second_budget_K4 S (by simp) hc hpair)
    (by simpa using hlist)

/-- **Scalar Reed–Solomon Rate `1/16`, `J+1` (`e = 805,306,371`, `B₂ = 2³¹`)**:
Any worst-center list exceeding `2³¹` forces 4 distinct degree-`< 2²⁶` polynomials whose
6 pairwise differences all split completely into `2²⁶ - 1` roots in the domain! -/
theorem rate_sixteenth_second_budget_rs_K4 {F : Type} [Field F] (D : Fin 1073741824 ↪ F)
    (hlist : ((2147483648 : ℕ) : ℕ∞) <
      Code.Lambda (ReedSolomon.code D 67108864 : Set (Fin 1073741824 → F))
        (((1073741824 - 268435453 : ℕ) : ℝ) / 1073741824)) :
    ∃ (y : Fin 1073741824 → F) (P : Fin 2147483649 → Polynomial F)
      (S : Fin 2147483649 → Finset (Fin 1073741824)),
      Function.Injective P ∧ (∀ i, (P i).natDegree < 67108864) ∧ (∀ i, (S i).card = 268435453) ∧
      (∀ i x, x ∈ S i → (P i).eval (D x) = y x) ∧ ¬ (fullGraph S 67108863).CliqueFree 4 :=
  from_list_rs D (by norm_num) (by simp only [Fintype.card_fin]; norm_num)
    (by simp only [Fintype.card_fin]; norm_num)
    (fun S hc hpair => rate_sixteenth_second_budget_K4 S (by simp) hc hpair)
    (by simpa using hlist)

end ProductionForcedCliques

end ProximityGap.QuadraticHahnCliques

#print axioms ProximityGap.QuadraticHahnCliques.forced_edges_quadratic_hahn
#print axioms ProximityGap.QuadraticHahnCliques.forced_clique_quadratic_hahn
#print axioms ProximityGap.QuadraticHahnCliques.rate_half_second_budget_K4
#print axioms ProximityGap.QuadraticHahnCliques.rate_sixteenth_second_budget_K4
#print axioms ProximityGap.QuadraticHahnCliques.rate_eighth_j2_second_budget_edges
#print axioms ProximityGap.QuadraticHahnCliques.rate_half_second_budget_rs_K4
#print axioms ProximityGap.QuadraticHahnCliques.rate_sixteenth_second_budget_rs_K4
