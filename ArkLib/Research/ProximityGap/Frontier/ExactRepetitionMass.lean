/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ExactRepetitionMassUpper
import ArkLib.Research.ProximityGap.Frontier.RepetitionSecondPrimeThreshold
import ArkLib.Research.ProximityGap.Frontier.RepetitionFirstPrimeThreshold
import ArkLib.Data.CodingTheory.ProximityGap.MCAExactComputationKit

/-! # Exact dimension-one MCA curve across production radii

Formalizes the complete exact dimension-one MCA curve of
`docs/research/proximity-gap/exact-repetition-mass.md`:

1. **Generic plane lower bound (`epsMCA_ge_candidate_pair` / `epsMCA_ge_exactMass`):**
   Over every finite field `F` with `4 * n ^ 3 < |F|`, every injective domain `dom : Fin n ↪ F`,
   every positive interleaving width `width`, and every integer agreement count `2 ≤ t ≤ n`,
   for every feasible `(h, r)` (`1 ≤ h ≤ n / (t - 1)`, `r < t`, `r * t - C(r, 2) ≤ n - h * (t - 1)`),
   there exists a two-row stack whose bad-scalar set has size at least
   `h * (n - h * (t - 1)) + C(h, 2) + r`. Maximizing over `(h, r)` gives
   `exactMass n t / |F| ≤ epsMCA ((ReedSolomon.code dom 1) ^⋈ Fin width) δ`
   whenever `⌈(1 - δ) * n⌉₊ ≤ t`.

2. **Exact dimension-one MCA equality (`exact_repetition_epsMCA` & `exact_repetition_epsMCA_concurrency`):**
   Combining the generic lower bound with `ExactRepetitionMassUpper.uniform_arrangement_upper`
   and `ExactRepetitionMassUpper.lines_card_le_of_three_mul_gt`, for every finite field with
   `4 * n ^ 3 < |F|`, every injective domain `dom : Fin n ↪ F`, every positive width, and every
   `δ : ℝ≥0` with `t = ⌈(1 - δ) * n⌉₊`:
   * If `2048 ≤ t ≤ n` and `256 * n ≤ t ^ 2`, then
     `epsMCA ((ReedSolomon.code dom 1) ^⋈ Fin width) δ = exactMass n t / |F|`.
   * If `2 ≤ t ≤ n` and `2 * n < 3 * t`, then
     `epsMCA ((ReedSolomon.code dom 1) ^⋈ Fin width) δ = (n - t + 1) / |F|`.

3. **Production corollaries at `n = 2^30` on both designated primes `p₁` and `p₂`:**
   Since `256 * 2^30 = (2^19)^2` and `4 * (2^30)^3 = 2^92 < p₁ < p₂`, the exact formula holds
   uniformly across `524,288 ≤ t ≤ 2^30` (strictly covering the entire production range
   `2^21 ≤ t ≤ 2^30`), together with verified exact values at all boundary rows of the
   exact-repetition-mass ledger.
-/

set_option autoImplicit false
noncomputable section

open Finset Polynomial Code
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.ExactRepetitionMass

open _root_.ProximityGap
open _root_.ProximityGap.MCAExactKit
open _root_.ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.Frontier.WeightedRichLinePacking
open ArkLib.ProximityGap.Frontier.ExactRepetitionMassUpper

section DimOneMcaEvent

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]

omit [Nonempty I] [DecidableEq I] [Fintype F] in
/-- Dimension-one `mcaEvent` criterion: if `u 0 i + γ * u 1 i = c` on a coordinate set `S` of
size at least `⌈(1 - δ) * |I|⌉₊`, and `(u 0, u 1)` takes at least two distinct values on `S`,
then `γ` is an MCA bad scalar for `ReedSolomon.code dom 1`. -/
theorem mcaEvent_dim1_of_line (dom : I ↪ F) (δ : ℝ≥0) (u : WordStack F (Fin 2) I) (γ c : F)
    (S : Finset I) (hcard : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ ≤ S.card)
    (hline : ∀ i ∈ S, u 0 i + γ * u 1 i = c)
    (hnonconst : ∃ i ∈ S, ∃ j ∈ S, (u 0 i, u 1 i) ≠ (u 0 j, u 1 j)) :
    mcaEvent (F := F) (ReedSolomon.code dom 1 : Set (I → F)) δ (u 0) (u 1) γ := by
  rw [mcaEvent_iff_mcaEventNat_ceil]
  refine ⟨S, hcard, ?_, ?_⟩
  · refine ⟨fun _ => c, ?_, fun i hi => by simpa [smul_eq_mul] using (hline i hi).symm⟩
    change (fun _ => c) ∈ ReedSolomon.code dom 1
    rw [ReedSolomon.mem_code_iff_exists_polynomial]
    refine ⟨C c, degree_le_natDegree.trans_lt (by simp), ?_⟩
    ext i
    simp [ReedSolomon.evalOnPoints]
  · rintro ⟨v₀, hv₀, v₁, hv₁, hagree⟩
    change v₀ ∈ ReedSolomon.code dom 1 at hv₀
    change v₁ ∈ ReedSolomon.code dom 1 at hv₁
    rw [ReedSolomon.mem_code_iff_exists_polynomial] at hv₀ hv₁
    obtain ⟨p₀, hp₀, rfl⟩ := hv₀
    obtain ⟨p₁, hp₁, rfl⟩ := hv₁
    have hdeg0 : p₀.natDegree ≤ 0 := by
      by_cases hz : p₀ = 0
      · simp [hz]
      · rw [Polynomial.degree_eq_natDegree hz] at hp₀
        exact (Nat.lt_one_iff.mp (WithBot.coe_lt_coe.mp hp₀)).le
    have hdeg1 : p₁.natDegree ≤ 0 := by
      by_cases hz : p₁ = 0
      · simp [hz]
      · rw [Polynomial.degree_eq_natDegree hz] at hp₁
        exact (Nat.lt_one_iff.mp (WithBot.coe_lt_coe.mp hp₁)).le
    have hp₀C := eq_C_of_natDegree_le_zero hdeg0
    have hp₁C := eq_C_of_natDegree_le_zero hdeg1
    obtain ⟨i, hi, j, hj, hne⟩ := hnonconst
    apply hne
    have hi0 := (hagree i hi).1
    have hi1 := (hagree i hi).2
    have hj0 := (hagree j hj).1
    have hj1 := (hagree j hj).2
    simp only [ReedSolomon.evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk] at hi0 hi1 hj0 hj1
    rw [hp₀C, eval_C] at hi0 hj0
    rw [hp₁C, eval_C] at hi1 hj1
    exact Prod.ext (hi0.symm.trans hj0) (hi1.symm.trans hj1)

/-- General real-radius upper bound for dimension-one codes from an arrangement packing bound. -/
theorem epsMCA_le_of_arrangement_bound {N t B : ℕ} [NeZero N] (dom : Fin N ↪ F) (δ : ℝ≥0)
    (ht : 0 < t) (hceil : t ≤ ⌈(1 - δ) * (N : ℝ≥0)⌉₊)
    (bound : ∀ A : Arrangement (F × F) F t, mass A.w A.points = N → A.lines.card ≤ B)
    (width : ℕ) [NeZero width] :
    epsMCA (F := F) ((ReedSolomon.code dom 1 : Set (Fin N → F)) ^⋈ (Fin width)) δ ≤
      (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  classical
  rw [epsMCA_interleaved_eq]
  apply epsMCA_le_of_badCount_le
  intro u
  obtain ⟨fam, eq⟩ :=
    HalfPredecessorBadEventRichPointBridge.exists_richPointFamily_with_badScalar_count
      dom δ u (by decide : 1 ≤ 1)
  rw [eq]
  obtain ⟨A, lines, hm⟩ := RepetitionSecondPrimeThreshold.arrangement fam t (by
    simpa [Fintype.card_fin] using hceil) ht
  rw [← lines]
  exact bound A (by simpa using hm)

end DimOneMcaEvent

/-! ## Section 2: Generic plane lower construction for `4 * n ^ 3 < |F|` -/

section GenericPlaneLower

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Slope/direction `γ` of the nonvertical line `b + γ * a = c` joining `p` and `q`. -/
private def dir (p q : F × F) : F := -(p.1 - q.1) / (p.2 - q.2)

omit [Fintype F] [DecidableEq F] in
private theorem dir_line_eq {p q : F × F} (hne : p.2 ≠ q.2) :
    p.1 + dir p q * p.2 = q.1 + dir p q * q.2 := by
  unfold dir
  have hsub : p.2 - q.2 ≠ 0 := sub_ne_zero.mpr hne
  field_simp [hsub]
  ring

omit [Fintype F] [DecidableEq F] in
private theorem eq_dir_of_line_eq {p q : F × F} {γ : F} (hne : p.2 ≠ q.2)
    (heq : p.1 + γ * p.2 = q.1 + γ * q.2) : γ = dir p q := by
  unfold dir
  have hsub : p.2 - q.2 ≠ 0 := sub_ne_zero.mpr hne
  field_simp [hsub]
  linear_combination heq

/-- Vertical line `{ (b, y) | b ∈ F }` in `F × F` (cardinality `|F|`). -/
private def verticalLine (y : F) : Finset (F × F) :=
  Finset.univ.image (fun b : F => (b, y))

omit [Field F] in
private theorem card_verticalLine (y : F) : (verticalLine y).card ≤ Fintype.card F :=
  Finset.card_image_le.trans (by simp)

omit [Field F] in
private theorem mem_verticalLine_iff {y : F} {x : F × F} : x ∈ verticalLine y ↔ x.2 = y := by
  simp only [verticalLine, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨b, hb⟩ => by rw [← hb], fun h => ⟨x.1, Prod.ext rfl h.symm⟩⟩

/-- Nonvertical line `{ x ∈ F × F | x.1 + γ * x.2 = p.1 + γ * p.2 }` (cardinality `|F|`). -/
private def affineLine (γ : F) (p : F × F) : Finset (F × F) :=
  Finset.univ.image (fun a : F => (p.1 + γ * p.2 - γ * a, a))

private theorem card_affineLine (γ : F) (p : F × F) : (affineLine γ p).card ≤ Fintype.card F :=
  Finset.card_image_le.trans (by simp)

private theorem mem_affineLine_iff {γ : F} {p x : F × F} :
    x ∈ affineLine γ p ↔ x.1 + γ * x.2 = p.1 + γ * p.2 := by
  simp only [affineLine, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha⟩
    rw [← ha]
    ring
  · intro h
    refine ⟨x.2, Prod.ext ?_ rfl⟩
    linear_combination -h

/-- Inductive center-selection lemma: whenever `|P| + |P|^2 + |P| * |D| < |F|`, there exists a
new point `x ∈ F × F` off all vertical lines through `P`, off all secant lines joining pairs of
points in `P`, and off all lines through `P` with direction in `D`. -/
private theorem exists_good_center (P : Finset (F × F)) (D : Finset F)
    (hroom : P.card + P.card * P.card + P.card * D.card < Fintype.card F) :
    ∃ x : F × F,
      (∀ p ∈ P, x.2 ≠ p.2) ∧
      (∀ p ∈ P, ∀ q ∈ P, p ≠ q → dir x p ≠ dir x q) ∧
      (∀ p ∈ P, ∀ γ ∈ D, dir x p ≠ γ) := by
  let B₁ : Finset (F × F) := P.biUnion (fun p => verticalLine p.2)
  let B₂ : Finset (F × F) := (P ×ˢ P).biUnion (fun pq =>
    if pq.1.2 ≠ pq.2.2 then affineLine (dir pq.1 pq.2) pq.1 else ∅)
  let B₃ : Finset (F × F) := (P ×ˢ D).biUnion (fun pγ => affineLine pγ.2 pγ.1)
  let Bad := (B₁ ∪ B₂) ∪ B₃
  have hB₁ : B₁.card ≤ P.card * Fintype.card F := by
    calc
      B₁.card ≤ ∑ p ∈ P, (verticalLine p.2).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ P, Fintype.card F := Finset.sum_le_sum (fun p _ => card_verticalLine p.2)
      _ = P.card * Fintype.card F := by simp
  have hB₂ : B₂.card ≤ (P.card * P.card) * Fintype.card F := by
    calc
      B₂.card ≤ ∑ pq ∈ P ×ˢ P, (if pq.1.2 ≠ pq.2.2 then affineLine (dir pq.1 pq.2) pq.1 else ∅).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _pq ∈ P ×ˢ P, Fintype.card F := Finset.sum_le_sum fun pq _ => by
        split_ifs
        · exact card_affineLine _ _
        · simp
      _ = (P.card * P.card) * Fintype.card F := by simp [Finset.card_product]
  have hB₃ : B₃.card ≤ (P.card * D.card) * Fintype.card F := by
    calc
      B₃.card ≤ ∑ pγ ∈ P ×ˢ D, (affineLine pγ.2 pγ.1).card := Finset.card_biUnion_le
      _ ≤ ∑ _pγ ∈ P ×ˢ D, Fintype.card F := Finset.sum_le_sum (fun pγ _ => card_affineLine _ _)
      _ = (P.card * D.card) * Fintype.card F := by simp [Finset.card_product]
  have hBad : Bad.card < (Finset.univ : Finset (F × F)).card := by
    have hu1 := Finset.card_union_le (B₁ ∪ B₂) B₃
    have hu2 := Finset.card_union_le B₁ B₂
    have hq_pos : 0 < Fintype.card F := Fintype.card_pos
    have hsum : Bad.card ≤ (P.card + P.card * P.card + P.card * D.card) * Fintype.card F := by
      calc Bad.card ≤ (B₁ ∪ B₂).card + B₃.card := hu1
        _ ≤ B₁.card + B₂.card + B₃.card := Nat.add_le_add_right hu2 _
        _ ≤ P.card * Fintype.card F + (P.card * P.card) * Fintype.card F +
            (P.card * D.card) * Fintype.card F := Nat.add_le_add (Nat.add_le_add hB₁ hB₂) hB₃
        _ = (P.card + P.card * P.card + P.card * D.card) * Fintype.card F := by ring
    have hlt : (P.card + P.card * P.card + P.card * D.card) * Fintype.card F <
        Fintype.card F * Fintype.card F := Nat.mul_lt_mul_of_pos_right hroom hq_pos
    simpa [Fintype.card_prod] using hsum.trans_lt hlt
  have hne : ((Finset.univ : Finset (F × F)) \ Bad).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    omega
  obtain ⟨x, hx⟩ := hne
  have hxBad : x ∉ Bad := (Finset.mem_sdiff.mp hx).2
  have hx1 : x ∉ B₁ := fun h => hxBad (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hx2 : x ∉ B₂ := fun h => hxBad (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hx3 : x ∉ B₃ := fun h => hxBad (Finset.mem_union_right _ h)
  have hvert : ∀ p ∈ P, x.2 ≠ p.2 := fun p hp heq =>
    hx1 (Finset.mem_biUnion.mpr ⟨p, hp, mem_verticalLine_iff.mpr heq⟩)
  refine ⟨x, hvert, ?_, ?_⟩
  · intro p hp q hq hpq hdir
    have hlinep := dir_line_eq (hvert p hp)
    have hlineq := dir_line_eq (hvert q hq)
    rw [hdir] at hlinep
    have hpq_line : p.1 + dir x q * p.2 = q.1 + dir x q * q.2 := hlinep.symm.trans hlineq
    by_cases h2 : p.2 = q.2
    · apply hpq
      refine Prod.ext ?_ h2
      rw [h2] at hpq_line
      exact add_right_cancel hpq_line
    · have hγ : dir x q = dir p q := eq_dir_of_line_eq h2 hpq_line
      apply hx2
      refine Finset.mem_biUnion.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, ?_⟩
      simp only [h2, ne_eq, not_false_eq_true, ↓reduceIte, mem_affineLine_iff, ← hγ]
      exact hlinep
  · intro p hp γ hγ hdir
    apply hx3
    refine Finset.mem_biUnion.mpr ⟨(p, γ), Finset.mem_product.mpr ⟨hp, hγ⟩, ?_⟩
    rw [mem_affineLine_iff, ← hdir]
    exact dir_line_eq (hvert p hp)

/-- Place `L` distinct light points in `F × F` carrying `r` nonvertical lines `b + g_j * a = g_j^2`
each containing at least `t` of the light points, whenever `r < t ≤ n`, `L ≤ n`,
`lightLineMass r t ≤ L`, and `4 * n ^ 3 < |F|`. -/
private theorem exists_light_points_with_lines {n t r L : ℕ} (_ht : 2 ≤ t) (htn : t ≤ n)
    (hrt : r < t) (hLn : L ≤ n) (hmass : lightLineMass r t ≤ L)
    (hF : 4 * n ^ 3 < Fintype.card F) :
    ∃ (g : Fin r ↪ F) (Light : Finset (F × F)),
      Light.card = L ∧
      ∀ j : Fin r, t ≤ (Light.filter (fun p => p.1 + g j * p.2 = (g j) ^ 2)).card := by
  classical
  have hn_pos : 1 ≤ n := by omega
  have hn_lt_F : n < Fintype.card F := by
    have : n ≤ 4 * n ^ 3 := by
      calc n = 1 * n := (one_mul n).symm
        _ ≤ 4 * n ^ 2 * n := Nat.mul_le_mul_right n (by nlinarith only [hn_pos])
        _ = 4 * n ^ 3 := by ring
    omega
  obtain ⟨S_g, _, hS_g_card⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F))
    (show r ≤ (Finset.univ : Finset F).card by rw [Finset.card_univ]; omega)
  have hS_g_coe : Fintype.card S_g = r := by simpa using hS_g_card
  let g : Fin r ↪ F := (Fintype.equivFinOfCardEq hS_g_coe).symm.toEmbedding.trans
    (Function.Embedding.subtype (· ∈ S_g))
  let interPt (i j : Fin r) : F × F := (-(g i * g j), g i + g j)
  have hinter_on_left (i j : Fin r) : (interPt i j).1 + g i * (interPt i j).2 = (g i) ^ 2 := by
    dsimp [interPt]; ring
  have hinter_on_right (i j : Fin r) : (interPt i j).1 + g j * (interPt i j).2 = (g j) ^ 2 := by
    dsimp [interPt]; ring
  let pairs := ((Finset.univ : Finset (Fin r)) ×ˢ (Finset.univ : Finset (Fin r))).filter
    (fun ij => ij.1 < ij.2)
  have hpairs_inj : Set.InjOn (fun ij : Fin r × Fin r => interPt ij.1 ij.2) (pairs : Set _) := by
    intro ⟨i, j⟩ hij ⟨i', j'⟩ hij' heq
    have hlt : i < j := (Finset.mem_filter.mp hij).2
    have hlt' : i' < j' := (Finset.mem_filter.mp hij').2
    have h1 : g i * g j = g i' * g j' := neg_injective (Prod.mk.inj heq).1
    have h2 : g i + g j = g i' + g j' := (Prod.mk.inj heq).2
    have hfac : (g i - g i') * (g i - g j') = 0 := by
      have : (g i - g i') * (g i - g j') = (g i) ^ 2 - (g i' + g j') * g i + g i' * g j' := by ring
      rw [this, ← h2, ← h1]; ring
    rcases mul_eq_zero.mp hfac with ha | hb
    · have hi : i = i' := g.injective (sub_eq_zero.mp ha)
      subst hi
      have hj : j = j' := g.injective (add_left_cancel h2)
      subst hj; rfl
    · have hi : i = j' := g.injective (sub_eq_zero.mp hb)
      subst hi
      have hj : j = i' := g.injective (by linear_combination h2)
      subst hj
      exact (lt_asymm hlt hlt').elim
  let S_inter : Finset (F × F) := pairs.image (fun ij => interPt ij.1 ij.2)
  have hS_inter_card : S_inter.card = r.choose 2 := by
    rw [Finset.card_image_of_injOn hpairs_inj]
    have hbij : pairs.card = ((Finset.univ : Finset (Fin r)).powersetCard 2).card := by
      refine Finset.card_bij (fun ij _ => ({ij.1, ij.2} : Finset (Fin r))) ?_ ?_ ?_
      · intro ⟨i, j⟩ hij
        have hlt : i < j := (Finset.mem_filter.mp hij).2
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, Finset.card_pair (ne_of_lt hlt)⟩
      · intro ⟨i, j⟩ hij ⟨i', j'⟩ hij' heq
        have hlt : i < j := (Finset.mem_filter.mp hij).2
        have hlt' : i' < j' := (Finset.mem_filter.mp hij').2
        have hi_mem : i ∈ ({i', j'} : Finset (Fin r)) := by rw [← heq]; simp
        have hj_mem : j ∈ ({i', j'} : Finset (Fin r)) := by rw [← heq]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi_mem hj_mem
        rcases hi_mem with rfl | rfl <;> rcases hj_mem with rfl | rfl
        · exact (lt_irrefl _ hlt).elim
        · rfl
        · exact (lt_asymm hlt hlt').elim
        · exact (lt_irrefl _ hlt).elim
      · intro T hT
        rw [Finset.mem_powersetCard] at hT
        obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hT.2
        rcases lt_or_gt_of_ne hab with hlt | hgt
        · exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hlt⟩, rfl⟩
        · exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hgt⟩,
            Finset.pair_comm b a⟩
    rw [hbij, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hS_inter_on (j : Fin r) :
      r - 1 ≤ (S_inter.filter (fun p => p.1 + g j * p.2 = (g j) ^ 2)).card := by
    let others : Finset (Fin r) := Finset.univ.erase j
    let f : Fin r → F × F := fun i => interPt i j
    have hf_sub : others.image f ⊆ S_inter.filter (fun p => p.1 + g j * p.2 = (g j) ^ 2) := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      have hij : i ≠ j := (Finset.mem_erase.mp hi).1
      refine Finset.mem_filter.mpr ⟨?_, hinter_on_right i j⟩
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hlt⟩, rfl⟩
      · refine Finset.mem_image.mpr ⟨(j, i), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hgt⟩, ?_⟩
        dsimp [interPt, f]
        exact Prod.ext (by ring) (by ring)
    have hf_inj : Set.InjOn f (others : Set (Fin r)) := fun i₁ _ i₂ _ heq => by
      have h2 : g i₁ + g j = g i₂ + g j := (Prod.mk.inj heq).2
      exact g.injective (add_right_cancel h2)
    have hcard : (others.image f).card = r - 1 := by
      rw [Finset.card_image_of_injOn hf_inj, Finset.card_erase_of_mem (Finset.mem_univ j),
        Finset.card_univ, Fintype.card_fin]
    exact hcard ▸ Finset.card_le_card hf_sub
  let m := t - (r - 1)
  have hm_room (j : Fin r) : m ≤ (Finset.univ \ (Finset.univ.image (fun k : Fin r => g j + g k))).card := by
    have hle : (Finset.univ.image (fun k : Fin r => g j + g k)).card ≤ r :=
      Finset.card_image_le.trans (by simp)
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    omega
  have hextra : ∀ j : Fin r, ∃ E : Finset F, E.card = m ∧
      ∀ a ∈ E, ∀ k : Fin r, a ≠ g j + g k := fun j => by
    obtain ⟨E, hEsub, hEcard⟩ := Finset.exists_subset_card_eq (hm_room j)
    refine ⟨E, hEcard, fun a ha k heq => ?_⟩
    have hnot := (Finset.mem_sdiff.mp (hEsub ha)).2
    exact hnot (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, heq.symm⟩)
  choose extraA hextra_card hextra_avoid using hextra
  let lift (j : Fin r) (a : F) : F × F := ((g j) ^ 2 - g j * a, a)
  let Extra (j : Fin r) : Finset (F × F) := (extraA j).image (lift j)
  have hExtra_card (j : Fin r) : (Extra j).card = m := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2), hextra_card j]
  have hExtra_on (j : Fin r) : ∀ p ∈ Extra j, p.1 + g j * p.2 = (g j) ^ 2 := by
    intro p hp
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    dsimp [lift]; ring
  have hExtra_not_other (j k : Fin r) (hjk : j ≠ k) :
      ∀ p ∈ Extra j, p.1 + g k * p.2 ≠ (g k) ^ 2 := by
    intro p hp heq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    dsimp [lift] at heq
    have hfac : (g k - g j) * (a - (g j + g k)) = 0 := by linear_combination heq
    rcases mul_eq_zero.mp hfac with h1 | h2
    · exact hjk (g.injective (sub_eq_zero.mp h1)).symm
    · exact hextra_avoid j a ha k (sub_eq_zero.mp h2)
  have hExtra_disj : (Set.univ : Set (Fin r)).PairwiseDisjoint Extra := by
    intro j _ k _ hjk
    change Disjoint (Extra j) (Extra k)
    rw [Finset.disjoint_left]
    intro p hpj hpk
    exact hExtra_not_other j k hjk p hpj (hExtra_on k p hpk)
  have hExtra_disj_inter (j : Fin r) : Disjoint (Extra j) S_inter := by
    rw [Finset.disjoint_left]
    intro p hpE hpI
    obtain ⟨⟨i₁, i₂⟩, hij, rfl⟩ := Finset.mem_image.mp hpI
    have hlt : i₁ < i₂ := (Finset.mem_filter.mp hij).2
    by_cases h1 : j = i₁
    · exact hExtra_not_other j i₂ (h1 ▸ ne_of_lt hlt) _ hpE (hinter_on_right i₁ i₂)
    · exact hExtra_not_other j i₁ h1 _ hpE (hinter_on_left i₁ i₂)
  let Base : Finset (F × F) := S_inter ∪ (Finset.univ : Finset (Fin r)).biUnion Extra
  have hBase_card : Base.card = lightLineMass r t := by
    have hdisj_bi : Disjoint S_inter ((Finset.univ : Finset (Fin r)).biUnion Extra) :=
      Finset.disjoint_right.mpr fun p hp hpI => by
        obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp
        exact Finset.disjoint_left.mp (hExtra_disj_inter j) hj hpI
    rw [Finset.card_union_of_disjoint hdisj_bi, hS_inter_card,
      Finset.card_biUnion (fun j _ k _ hjk => hExtra_disj (Set.mem_univ j) (Set.mem_univ k) hjk)]
    simp only [hExtra_card, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    unfold lightLineMass m
    have h2c := two_mul_choose_two r
    have hcm := choose_two_le_mul r t (Nat.le_of_lt hrt)
    rcases Nat.eq_zero_or_pos r with rfl | hrpos
    · simp
    · have hrr : r * (r - 1) ≤ r * t := Nat.mul_le_mul_left r (by omega)
      have hsub1 : r * (t - (r - 1)) = r * t - r * (r - 1) := Nat.mul_sub_left_distrib r t (r - 1)
      rw [← h2c] at hrr
      rw [hsub1, ← h2c]
      omega
  have hpad_room : L - Base.card ≤ ((Finset.univ : Finset (F × F)) \ Base).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_prod]
    have hq2 : Fintype.card F ≤ Fintype.card F * Fintype.card F := Nat.le_mul_self _
    omega
  obtain ⟨Pad, hPad_sub, hPad_card⟩ := Finset.exists_subset_card_eq hpad_room
  let Light := Base ∪ Pad
  have hLight_card : Light.card = L := by
    have hdisj : Disjoint Base Pad :=
      Finset.disjoint_of_subset_right hPad_sub disjoint_sdiff_self_right
    rw [Finset.card_union_of_disjoint hdisj, hPad_card]
    omega
  refine ⟨g, Light, hLight_card, fun j => ?_⟩
  have hsub1 : S_inter.filter (fun p => p.1 + g j * p.2 = (g j) ^ 2) ⊆
      Light.filter (fun p => p.1 + g j * p.2 = (g j) ^ 2) :=
    Finset.filter_subset_filter _ (Finset.subset_union_left.trans Finset.subset_union_left)
  have hsub2 : Extra j ⊆ Light.filter (fun p => p.1 + g j * p.2 = (g j) ^ 2) := fun p hp =>
    Finset.mem_filter.mpr
      ⟨Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hp⟩)),
       hExtra_on j p hp⟩
  have hdisj_j : Disjoint (S_inter.filter (fun p => p.1 + g j * p.2 = (g j) ^ 2)) (Extra j) :=
    Finset.disjoint_of_subset_left (Finset.filter_subset _ _) (hExtra_disj_inter j).symm
  have hcard_u := Finset.card_le_card (Finset.union_subset hsub1 hsub2)
  rw [Finset.card_union_of_disjoint hdisj_j, hExtra_card j] at hcard_u
  have hsi := hS_inter_on j
  omega

/-- Inductive addition of `k` generic centers on top of `Light` (`|Light| = L`) and `r` prescribed
directions `G₀` (`|G₀| = r`). Every direction in `D` is either in `G₀`, a center-light secant,
or a center-center secant, and `|D| = r + k * L + C(k, 2)`. -/
private theorem exists_centers_ind {n L r : ℕ} (k : ℕ) (hLk : L + k ≤ n) (hrn : r ≤ n)
    (hF : 4 * n ^ 3 < Fintype.card F)
    (Light : Finset (F × F)) (hL : Light.card = L) (G₀ : Finset F) (hG₀ : G₀.card = r) :
    ∃ (C : Finset (F × F)) (D : Finset F),
      Disjoint C Light ∧ C.card = k ∧ D.card = r + k * L + k.choose 2 ∧
      ∀ γ ∈ D,
        γ ∈ G₀ ∨
        (∃ c ∈ C, ∃ p ∈ Light, c.2 ≠ p.2 ∧ γ = dir c p) ∨
        (∃ c₁ ∈ C, ∃ c₂ ∈ C, c₁ ≠ c₂ ∧ c₁.2 ≠ c₂.2 ∧ γ = dir c₁ c₂) := by
  induction k with
  | zero =>
    refine ⟨∅, G₀, by simp, by simp, by simp [hG₀], fun γ hγ => Or.inl hγ⟩
  | succ k ih =>
    obtain ⟨C, D, hdisj, hCcard, hDcard, hDmem⟩ := ih (by omega)
    let P := Light ∪ C
    have hPcard : P.card = L + k := by
      rw [Finset.card_union_of_disjoint hdisj.symm, hL, hCcard]
    have hP_le : P.card ≤ n := by omega
    have hD_le : D.card ≤ n + n * n := by
      have h2 := two_mul_choose_two k
      have hch : k.choose 2 ≤ k * k := by
        have hkm : k * (k - 1) ≤ k * k := Nat.mul_le_mul_left k (Nat.sub_le k 1)
        omega
      have hsum_le : k * L + k.choose 2 ≤ k * (L + k) := by rw [Nat.mul_add]; omega
      have hkn : k * (L + k) ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
      omega
    have hroom : P.card + P.card * P.card + P.card * D.card < Fintype.card F := by
      have hn_pos : 1 ≤ n := by omega
      have h1 : P.card ≤ n ^ 3 := by
        calc P.card ≤ n := hP_le
          _ = 1 * n := (one_mul n).symm
          _ ≤ n ^ 2 * n := Nat.mul_le_mul_right n (by nlinarith only [hn_pos])
          _ = n ^ 3 := by ring
      have h2 : P.card * P.card ≤ n ^ 3 := by
        calc P.card * P.card ≤ n * n := Nat.mul_le_mul hP_le hP_le
          _ = n ^ 2 * 1 := by ring
          _ ≤ n ^ 2 * n := Nat.mul_le_mul_left _ hn_pos
          _ = n ^ 3 := by ring
      have h3 : P.card * D.card ≤ 2 * n ^ 3 := by
        have hD2 : D.card ≤ 2 * n ^ 2 := by
          have : n ≤ n ^ 2 := by nlinarith only [hn_pos]
          nlinarith only [hD_le, this]
        calc P.card * D.card ≤ n * (2 * n ^ 2) := Nat.mul_le_mul hP_le hD2
          _ = 2 * n ^ 3 := by ring
      omega
    obtain ⟨x, hx_vert, hx_inj, hx_fresh⟩ := exists_good_center P D hroom
    have hx_notP : x ∉ P := fun hxP => hx_vert x hxP rfl
    have hx_notL : x ∉ Light := fun hxL => hx_notP (Finset.mem_union_left _ hxL)
    have hx_notC : x ∉ C := fun hxC => hx_notP (Finset.mem_union_right _ hxC)
    let newDirs := P.image (fun p => dir x p)
    have hnew_card : newDirs.card = L + k := by
      rw [Finset.card_image_of_injOn (fun p hp q hq heq => by
        by_contra hpq
        exact hx_inj p hp q hq hpq heq), hPcard]
    have hnew_disj : Disjoint D newDirs := by
      rw [Finset.disjoint_right]
      intro γ hγ hD
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hγ
      exact hx_fresh p hp (dir x p) hD rfl
    refine ⟨insert x C, D ∪ newDirs, ?_, ?_, ?_, ?_⟩
    · exact Finset.disjoint_insert_left.mpr ⟨hx_notL, hdisj⟩
    · rw [Finset.card_insert_of_notMem hx_notC, hCcard]
    · rw [Finset.card_union_of_disjoint hnew_disj, hDcard, hnew_card,
        Nat.choose_succ_succ, Nat.choose_one_right, Nat.succ_mul]
      change r + k * L + k.choose 2 + (L + k) = r + (k * L + L) + (k + k.choose 2)
      omega
    · intro γ hγ
      rcases Finset.mem_union.mp hγ with hD' | hnew
      · rcases hDmem γ hD' with hG | ⟨c, hc, p, hp, h2, hdir⟩ | ⟨c₁, hc₁, c₂, hc₂, hne, h2, hdir⟩
        · exact Or.inl hG
        · exact Or.inr (Or.inl ⟨c, Finset.mem_insert_of_mem hc, p, hp, h2, hdir⟩)
        · exact Or.inr (Or.inr ⟨c₁, Finset.mem_insert_of_mem hc₁, c₂, Finset.mem_insert_of_mem hc₂, hne, h2, hdir⟩)
      · obtain ⟨p, hpP, rfl⟩ := Finset.mem_image.mp hnew
        rcases Finset.mem_union.mp hpP with hpL | hpC
        · exact Or.inr (Or.inl ⟨x, Finset.mem_insert_self x C, p, hpL, hx_vert p hpP, rfl⟩)
        · exact Or.inr (Or.inr ⟨x, Finset.mem_insert_self x C, p, Finset.mem_insert_of_mem hpC,
            fun h => hx_notC (h ▸ hpC), hx_vert p hpP, rfl⟩)

/-- **Generic plane lower bound for any candidate `(h, r)`:**
Whenever `4 * n ^ 3 < |F|`, `2 ≤ t ≤ n`, `1 ≤ h`, `h * (t - 1) ≤ n`, `r < t`, and
`lightLineMass r t ≤ n - h * (t - 1)`, the dimension-one code of length `n` at any positive
interleaving width satisfies `epsMCA ≥ (h * (n - h * (t - 1)) + C(h, 2) + r) / |F|` for every
`δ : ℝ≥0` with `⌈(1 - δ) * n⌉₊ ≤ t`. -/
theorem epsMCA_ge_candidate_pair {n t h r : ℕ} [NeZero n] (dom : Fin n ↪ F) (δ : ℝ≥0)
    (ht : 2 ≤ t) (htn : t ≤ n) (_hh : 1 ≤ h) (hfeas : h * (t - 1) ≤ n)
    (hrt : r < t) (hmass : lightLineMass r t ≤ n - h * (t - 1))
    (hceil : ⌈(1 - δ) * (n : ℝ≥0)⌉₊ ≤ t) (hF : 4 * n ^ 3 < Fintype.card F)
    (width : ℕ) [NeZero width] :
    ((h * (n - h * (t - 1)) + h.choose 2 + r : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) ((ReedSolomon.code dom 1 : Set (Fin n → F)) ^⋈ (Fin width)) δ := by
  classical
  let L := n - h * (t - 1)
  have hLn : L ≤ n := Nat.sub_le _ _
  have hLh : L + h ≤ n := by
    have : h * 1 ≤ h * (t - 1) := Nat.mul_le_mul_left h (by omega)
    omega
  obtain ⟨g, Light, hLight_card, hLight_lines⟩ :=
    exists_light_points_with_lines (F := F) ht htn hrt hLn hmass hF
  let G₀ : Finset F := Finset.univ.image g
  have hG₀_card : G₀.card = r := by
    rw [Finset.card_image_of_injective _ g.injective, Finset.card_univ, Fintype.card_fin]
  obtain ⟨C, D, hdisj, hCcard, hDcard, hDmem⟩ :=
    exists_centers_ind h hLh (by omega) hF Light hLight_card G₀ hG₀_card
  let eC : Fin h ≃ C := (Fintype.equivFinOfCardEq (by simpa using hCcard)).symm
  let eL : Fin L ≃ Light := (Fintype.equivFinOfCardEq (by simpa using hLight_card)).symm
  let eIdx : ((Fin h × Fin (t - 1)) ⊕ Fin L) ≃ Fin n :=
    ((finProdFinEquiv.sumCongr (Equiv.refl _)).trans finSumFinEquiv).trans
      (finCongr (by omega : h * (t - 1) + L = n))
  let ptOf : ((Fin h × Fin (t - 1)) ⊕ Fin L) → F × F
    | .inl (i, _) => (eC i).val
    | .inr j => (eL j).val
  let pts : Fin n → F × F := fun idx => ptOf (eIdx.symm idx)
  let u : WordStack F (Fin 2) (Fin n) := ![fun idx => (pts idx).1, fun idx => (pts idx).2]
  have hpts_idx (z) : pts (eIdx z) = ptOf z := by simp [pts]
  let centerCoords (c : C) : Finset (Fin n) :=
    (Finset.univ : Finset (Fin (t - 1))).image (fun m => eIdx (.inl (eC.symm c, m)))
  have hcenterCoords_card (c : C) : (centerCoords c).card = t - 1 := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj (Sum.inl.inj (eIdx.injective h))).2),
      Finset.card_univ, Fintype.card_fin]
  have hcenterCoords_val (c : C) : ∀ idx ∈ centerCoords c, pts idx = c.val := by
    intro idx hidx
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hidx
    simp [hpts_idx, ptOf]
  let lightCoord (p : Light) : Fin n := eIdx (.inr (eL.symm p))
  have hlightCoord_val (p : Light) : pts (lightCoord p) = p.val := by
    simp [lightCoord, hpts_idx, ptOf]
  have hlightCoord_inj : Function.Injective lightCoord := fun p₁ p₂ h =>
    eL.symm.injective (Sum.inr.inj (eIdx.injective h))
  have hlight_not_center (p : Light) (c : C) : lightCoord p ∉ centerCoords c := by
    intro hmem
    obtain ⟨m, _, hm⟩ := Finset.mem_image.mp hmem
    have := eIdx.injective hm
    exact Sum.inl_ne_inr this
  have hcenter_disj {c₁ c₂ : C} (hne : c₁ ≠ c₂) : Disjoint (centerCoords c₁) (centerCoords c₂) := by
    rw [Finset.disjoint_left]
    intro idx h1 h2
    obtain ⟨m₁, _, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨m₂, _, hm2⟩ := Finset.mem_image.mp h2
    exact hne (eC.symm.injective (Prod.mk.inj (Sum.inl.inj (eIdx.injective hm2))).1.symm)
  have hceil' : ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ ≤ t := by
    simpa [Fintype.card_fin] using hceil
  have hevent : ∀ γ ∈ D, mcaEvent (F := F) (ReedSolomon.code dom 1 : Set (Fin n → F)) δ (u 0) (u 1) γ := by
    intro γ hγ
    rcases hDmem γ hγ with hG | ⟨c, hc, p, hp, h2, rfl⟩ | ⟨c₁, hc₁, c₂, hc₂, hne, h2, rfl⟩
    · -- Case 1: prescribed light-only line `g j`.
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hG
      let Lj := Light.filter (fun p => p.1 + g j * p.2 = (g j) ^ 2)
      let S : Finset (Fin n) := Lj.attach.image (fun p => lightCoord ⟨p.1, (Finset.mem_filter.mp p.2).1⟩)
      have hS_inj : Function.Injective (fun p : Lj => lightCoord ⟨p.1, (Finset.mem_filter.mp p.2).1⟩) := by
        intro p₁ p₂ heq
        have hval : p₁.1 = p₂.1 := congrArg (Subtype.val : Light → F × F) (hlightCoord_inj heq)
        exact Subtype.ext hval
      have hS_card : t ≤ S.card := by
        rw [Finset.card_image_of_injective _ hS_inj, Finset.card_attach]
        exact hLight_lines j
      apply mcaEvent_dim1_of_line dom δ u (g j) ((g j) ^ 2) S (hceil'.trans hS_card)
      · intro idx hidx
        obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hidx
        have hval := hlightCoord_val ⟨p.1, (Finset.mem_filter.mp p.2).1⟩
        change (pts _).1 + g j * (pts _).2 = (g j) ^ 2
        rw [hval]
        exact (Finset.mem_filter.mp p.2).2
      · have hLj_gt1 : 1 < Lj.card := by
          have htL : t ≤ Lj.card := hLight_lines j
          omega
        obtain ⟨p₁, hp₁, p₂, hp₂, hp12⟩ := Finset.one_lt_card.mp hLj_gt1
        let i₁ := lightCoord ⟨p₁, (Finset.mem_filter.mp hp₁).1⟩
        let i₂ := lightCoord ⟨p₂, (Finset.mem_filter.mp hp₂).1⟩
        refine ⟨i₁, Finset.mem_image.mpr ⟨⟨p₁, hp₁⟩, Finset.mem_attach _ _, rfl⟩,
                i₂, Finset.mem_image.mpr ⟨⟨p₂, hp₂⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
        change pts i₁ ≠ pts i₂
        rw [hlightCoord_val, hlightCoord_val]
        exact hp12
    · -- Case 2: center-light line `dir c p`.
      let S : Finset (Fin n) := insert (lightCoord ⟨p, hp⟩) (centerCoords ⟨c, hc⟩)
      have hS_card : S.card = t := by
        rw [Finset.card_insert_of_notMem (hlight_not_center ⟨p, hp⟩ ⟨c, hc⟩),
          hcenterCoords_card ⟨c, hc⟩]
        omega
      apply mcaEvent_dim1_of_line dom δ u (dir c p) (c.1 + dir c p * c.2) S (by omega)
      · intro idx hidx
        rcases Finset.mem_insert.mp hidx with rfl | hmemC
        · change (pts _).1 + dir c p * (pts _).2 = c.1 + dir c p * c.2
          rw [hlightCoord_val]
          exact (dir_line_eq h2).symm
        · change (pts idx).1 + dir c p * (pts idx).2 = c.1 + dir c p * c.2
          rw [hcenterCoords_val ⟨c, hc⟩ idx hmemC]
      · let i₀ := eIdx (.inl (eC.symm ⟨c, hc⟩, ⟨0, by omega⟩))
        have hi₀ : i₀ ∈ centerCoords ⟨c, hc⟩ :=
          Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, rfl⟩
        refine ⟨i₀, Finset.mem_insert_of_mem hi₀, lightCoord ⟨p, hp⟩, Finset.mem_insert_self _ _, ?_⟩
        change pts i₀ ≠ pts (lightCoord ⟨p, hp⟩)
        rw [hcenterCoords_val ⟨c, hc⟩ i₀ hi₀, hlightCoord_val]
        intro heq
        exact h2 (congrArg Prod.snd heq)
    · -- Case 3: center-center line `dir c₁ c₂`.
      let S : Finset (Fin n) := centerCoords ⟨c₁, hc₁⟩ ∪ centerCoords ⟨c₂, hc₂⟩
      have hne' : (⟨c₁, hc₁⟩ : C) ≠ ⟨c₂, hc₂⟩ := fun h => hne (congrArg Subtype.val h)
      have hS_card : t ≤ S.card := by
        rw [Finset.card_union_of_disjoint (hcenter_disj hne'),
          hcenterCoords_card, hcenterCoords_card]
        omega
      apply mcaEvent_dim1_of_line dom δ u (dir c₁ c₂) (c₁.1 + dir c₁ c₂ * c₁.2) S (hceil'.trans hS_card)
      · intro idx hidx
        rcases Finset.mem_union.mp hidx with h1 | h2'
        · change (pts idx).1 + dir c₁ c₂ * (pts idx).2 = c₁.1 + dir c₁ c₂ * c₁.2
          rw [hcenterCoords_val ⟨c₁, hc₁⟩ idx h1]
        · change (pts idx).1 + dir c₁ c₂ * (pts idx).2 = c₁.1 + dir c₁ c₂ * c₁.2
          rw [hcenterCoords_val ⟨c₂, hc₂⟩ idx h2']
          exact (dir_line_eq h2).symm
      · let i₁ := eIdx (.inl (eC.symm ⟨c₁, hc₁⟩, ⟨0, by omega⟩))
        let i₂ := eIdx (.inl (eC.symm ⟨c₂, hc₂⟩, ⟨0, by omega⟩))
        have hi₁ : i₁ ∈ centerCoords ⟨c₁, hc₁⟩ :=
          Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, rfl⟩
        have hi₂ : i₂ ∈ centerCoords ⟨c₂, hc₂⟩ :=
          Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, rfl⟩
        refine ⟨i₁, Finset.mem_union_left _ hi₁, i₂, Finset.mem_union_right _ hi₂, ?_⟩
        change pts i₁ ≠ pts i₂
        rw [hcenterCoords_val ⟨c₁, hc₁⟩ i₁ hi₁, hcenterCoords_val ⟨c₂, hc₂⟩ i₂ hi₂]
        exact hne
  rw [epsMCA_interleaved_eq]
  have hmass_eps := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (ReedSolomon.code dom 1 : Set (Fin n → F)) δ u D hevent
  have hD_eq : D.card = h * L + h.choose 2 + r := by omega
  simpa only [hD_eq] using hmass_eps

/-- Generic lower bound matching `candidateMass n t h`. -/
theorem epsMCA_ge_candidateMass {n t h : ℕ} [NeZero n] (dom : Fin n ↪ F) (δ : ℝ≥0)
    (ht : 2 ≤ t) (htn : t ≤ n) (hh : 1 ≤ h) (hfeas : h * (t - 1) ≤ n)
    (hceil : ⌈(1 - δ) * (n : ℝ≥0)⌉₊ ≤ t) (hF : 4 * n ^ 3 < Fintype.card F)
    (width : ℕ) [NeZero width] :
    (candidateMass n t h : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) ((ReedSolomon.code dom 1 : Set (Fin n → F)) ^⋈ (Fin width)) δ := by
  unfold candidateMass candidateQuad
  exact epsMCA_ge_candidate_pair dom δ ht htn hh hfeas
    (richLightCap_lt (by omega)) (lightLineMass_richLightCap_le (by omega)) hceil hF width

/-- Generic lower bound matching `exactMass n t`. -/
theorem epsMCA_ge_exactMass {n t : ℕ} [NeZero n] (dom : Fin n ↪ F) (δ : ℝ≥0)
    (ht : 2 ≤ t) (htn : t ≤ n) (hceil : ⌈(1 - δ) * (n : ℝ≥0)⌉₊ ≤ t)
    (hF : 4 * n ^ 3 < Fintype.card F) (width : ℕ) [NeZero width] :
    (exactMass n t : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) ((ReedSolomon.code dom 1 : Set (Fin n → F)) ^⋈ (Fin width)) δ := by
  have hmax_pos : 1 ≤ n / (t - 1) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hne : (Finset.Icc 1 (n / (t - 1))).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hmax_pos⟩⟩
  obtain ⟨h, hh_mem, hmax⟩ := Finset.exists_mem_eq_sup _ hne (candidateMass n t)
  obtain ⟨h1, hle⟩ := Finset.mem_Icc.mp hh_mem
  have hfeas : h * (t - 1) ≤ n := (Nat.le_div_iff_mul_le (by omega)).mp hle
  unfold exactMass
  rw [hmax]
  exact epsMCA_ge_candidateMass dom δ ht htn h1 hfeas hceil hF width

end GenericPlaneLower

/-! ## Section 3: Main exact dimension-one MCA curve theorems -/

section MainTheorems

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Exact dimension-one MCA curve (uniform regime):**
For every length `n`, every finite field `F` with `4 * n ^ 3 < |F|`, every injective domain
`dom : Fin n ↪ F`, every positive interleaving width, and every `δ : ℝ≥0` whose integer
agreement count `t = ⌈(1 - δ) * n⌉₊` satisfies `2048 ≤ t ≤ n` and `256 * n ≤ t ^ 2`,
the exact MCA error probability of the interleaved dimension-one Reed–Solomon code is
  `exactMass n t / |F|`. -/
theorem exact_repetition_epsMCA {n t : ℕ} [NeZero n] (dom : Fin n ↪ F) (δ : ℝ≥0)
    (hceil : ⌈(1 - δ) * (n : ℝ≥0)⌉₊ = t)
    (ht : 2048 ≤ t) (htn : t ≤ n) (hsq : 256 * n ≤ t ^ 2)
    (hF : 4 * n ^ 3 < Fintype.card F) (width : ℕ) [NeZero width] :
    epsMCA (F := F) ((ReedSolomon.code dom 1 : Set (Fin n → F)) ^⋈ (Fin width)) δ =
      (exactMass n t : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  apply le_antisymm
  · exact epsMCA_le_of_arrangement_bound dom δ (by omega) hceil.ge
      (fun A hA => uniform_arrangement_upper A hA ht htn hsq) width
  · exact epsMCA_ge_exactMass dom δ (by omega) htn hceil.le hF width

/-- **Exact dimension-one MCA curve (concurrency regime `3 * t > 2 * n`):**
For every `2 ≤ t ≤ n` with `2 * n < 3 * t` and `4 * n ^ 3 < |F|`,
`epsMCA = (n - t + 1) / |F|`. -/
theorem exact_repetition_epsMCA_concurrency {n t : ℕ} [NeZero n] (dom : Fin n ↪ F) (δ : ℝ≥0)
    (hceil : ⌈(1 - δ) * (n : ℝ≥0)⌉₊ = t)
    (ht : 2 ≤ t) (htn : t ≤ n) (hgt : 2 * n < 3 * t)
    (hF : 4 * n ^ 3 < Fintype.card F) (width : ℕ) [NeZero width] :
    epsMCA (F := F) ((ReedSolomon.code dom 1 : Set (Fin n → F)) ^⋈ (Fin width)) δ =
      ((n - t + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  apply le_antisymm
  · exact epsMCA_le_of_arrangement_bound dom δ (by omega) hceil.ge
      (fun A hA => lines_card_le_of_three_mul_gt A hA (by omega) htn hgt) width
  · rw [← exactMass_of_three_mul_gt ht htn hgt]
    exact epsMCA_ge_exactMass dom δ ht htn hceil.le hF width

/-- Grid-point agreement ceiling helper: for `e + t = n`, `⌈(1 - e / n) * n⌉₊ = t`. -/
theorem grid_agreement_ceil {n e t : ℕ} [NeZero n] (he : e + t = n) :
    ⌈(1 - ((e : ℝ≥0) / (n : ℝ≥0))) * (n : ℝ≥0)⌉₊ = t := by
  rw [tsub_mul, one_mul, div_mul_cancel₀ _ (by exact_mod_cast (NeZero.ne n)), ← Nat.cast_tsub]
  simpa only [show n - e = t by omega] using Nat.ceil_natCast t

end MainTheorems

/-! ## Section 4: Production corollaries at `n = 2^30` and exact table evaluations -/

section Production

private abbrev nProd : ℕ := 1073741824
private abbrev p₁ : ℕ := PrizeShapePrimeP30.P
private abbrev p₂ : ℕ := PrizeShapePrimeP30Second.P

local instance : Fact p₁.Prime := ⟨PrizeShapePrimeP30.prime_P⟩
local instance : Fact p₂.Prime := ⟨PrizeShapePrimeP30Second.prime_P⟩

/-- Exact evaluation criterion for `richLightCap L t` avoiding enumeration of `Finset.range t`. -/
theorem richLightCap_eq_of_bounds {L t r : ℕ} (hrt : r < t) (hle : lightLineMass r t ≤ L)
    (hgt : r + 1 < t → L < lightLineMass (r + 1) t) :
    richLightCap L t = r := by
  have hge : r ≤ richLightCap L t := le_richLightCap_of_le hrt hle
  have hle' : richLightCap L t ≤ r := by
    by_contra hlt
    push Not at hlt
    have hr1_le : r + 1 ≤ richLightCap L t := hlt
    have hr1_lt : r + 1 < t := lt_of_le_of_lt hr1_le (richLightCap_lt (by omega))
    have hmono := lightLineMass_mono hr1_le (Nat.le_of_lt (richLightCap_lt (by omega)))
    have hcap := lightLineMass_richLightCap_le (L := L) (by omega : 0 < t)
    have hstrict := hgt hr1_lt
    omega
  omega

/-- Production corollary at the first designated prime `p₁` for every agreement count
`524,288 ≤ t ≤ 2^30` (strictly covering the entire production range `2^21 ≤ t ≤ 2^30`). -/
theorem production_first_prime (dom : Fin nProd ↪ ZMod p₁) (δ : ℝ≥0) {t : ℕ}
    (hceil : ⌈(1 - δ) * (nProd : ℝ≥0)⌉₊ = t)
    (ht : 524288 ≤ t) (htn : t ≤ nProd) (width : ℕ) [NeZero width] :
    epsMCA (F := ZMod p₁) ((ReedSolomon.code dom 1 : Set (Fin nProd → ZMod p₁)) ^⋈ (Fin width)) δ =
      (exactMass nProd t : ℝ≥0∞) / (p₁ : ℝ≥0∞) := by
  have hsq : 256 * nProd ≤ t ^ 2 := by
    have h1 : 524288 * 524288 ≤ t * t := Nat.mul_le_mul ht ht
    have h2 : 256 * nProd = 524288 * 524288 := by decide
    rw [pow_two]; omega
  have hF : 4 * nProd ^ 3 < Fintype.card (ZMod p₁) := by rw [ZMod.card]; decide
  simpa only [ZMod.card] using exact_repetition_epsMCA dom δ hceil (by omega) htn hsq hF width

/-- Production corollary at the second designated prime `p₂` for every agreement count
`524,288 ≤ t ≤ 2^30` (strictly covering the entire production range `2^21 ≤ t ≤ 2^30`). -/
theorem production_second_prime (dom : Fin nProd ↪ ZMod p₂) (δ : ℝ≥0) {t : ℕ}
    (hceil : ⌈(1 - δ) * (nProd : ℝ≥0)⌉₊ = t)
    (ht : 524288 ≤ t) (htn : t ≤ nProd) (width : ℕ) [NeZero width] :
    epsMCA (F := ZMod p₂) ((ReedSolomon.code dom 1 : Set (Fin nProd → ZMod p₂)) ^⋈ (Fin width)) δ =
      (exactMass nProd t : ℝ≥0∞) / (p₂ : ℝ≥0∞) := by
  have hsq : 256 * nProd ≤ t ^ 2 := by
    have h1 : 524288 * 524288 ≤ t * t := Nat.mul_le_mul ht ht
    have h2 : 256 * nProd = 524288 * 524288 := by decide
    rw [pow_two]; omega
  have hF : 4 * nProd ^ 3 < Fintype.card (ZMod p₂) := by rw [ZMod.card]; decide
  simpa only [ZMod.card] using exact_repetition_epsMCA dom δ hceil (by omega) htn hsq hF width

/-- Exact ledger evaluations at `n = 2^30` for the four designated-prime threshold boundary rows
and the lower-regime anchors `t = 2^21` and `t = 2^19`. -/
theorem exactMass_production_table :
    exactMass nProd 268435458 = 1073741822 ∧
    exactMass nProd 268435457 = 1073741826 ∧
    exactMass nProd 134217730 = 2147483641 ∧
    exactMass nProd 134217729 = 2147483658 ∧
    exactMass nProd 2097152 = 137439051904 ∧
    exactMass nProd 524288 = 549757387265 := by
  have eval_row : ∀ (t lo hi rlo rhi ans : ℕ),
      2048 ≤ t → t ≤ nProd → 256 * nProd ≤ t ^ 2 →
      candidateLow nProd t = lo → candidateHigh nProd t = hi →
      rlo < t → rlo * t - rlo * (rlo - 1) / 2 ≤ nProd - lo * (t - 1) →
      (rlo + 1 < t → nProd - lo * (t - 1) < (rlo + 1) * t - (rlo + 1) * rlo / 2) →
      rhi < t → rhi * t - rhi * (rhi - 1) / 2 ≤ nProd - hi * (t - 1) →
      (rhi + 1 < t → nProd - hi * (t - 1) < (rhi + 1) * t - (rhi + 1) * rhi / 2) →
      max (lo * (nProd - lo * (t - 1)) + lo * (lo - 1) / 2 + rlo)
          (hi * (nProd - hi * (t - 1)) + hi * (hi - 1) / 2 + rhi) = ans →
      exactMass nProd t = ans := by
    intro t lo hi rlo rhi ans ht htn hsq hlo hhi h1 h2 h3 h4 h5 h6 hans
    rw [exactMass_eq_two_candidates ht htn hsq, hlo, hhi]
    unfold candidateMass candidateQuad
    have hrl : richLightCap (nProd - lo * (t - 1)) t = rlo :=
      richLightCap_eq_of_bounds h1 (by unfold lightLineMass; rw [choose_two_eq]; exact h2)
        (fun hlt => by unfold lightLineMass; rw [choose_two_eq]; exact h3 hlt)
    have hrh : richLightCap (nProd - hi * (t - 1)) t = rhi :=
      richLightCap_eq_of_bounds h4 (by unfold lightLineMass; rw [choose_two_eq]; exact h5)
        (fun hlt => by unfold lightLineMass; rw [choose_two_eq]; exact h6 hlt)
    rw [hrl, hrh, choose_two_eq, choose_two_eq, hans]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact eval_row 268435458 1 2 2 1 1073741822 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (fun _ => by decide)
      (by decide) (by decide) (fun _ => by decide) (by decide)
  · exact eval_row 268435457 2 3 1 0 1073741826 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (fun _ => by decide)
      (by decide) (by decide) (fun _ => by decide) (by decide)
  · exact eval_row 134217730 3 4 4 3 2147483641 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (fun _ => by decide)
      (by decide) (by decide) (fun _ => by decide) (by decide)
  · exact eval_row 134217729 4 5 4 3 2147483658 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (fun _ => by decide)
      (by decide) (by decide) (fun _ => by decide) (by decide)
  · exact eval_row 2097152 256 257 256 255 137439051904 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (fun _ => by decide)
      (by decide) (by decide) (fun _ => by decide) (by decide)
  · exact eval_row 524288 1024 1025 1025 1024 549757387265 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (fun _ => by decide)
      (by decide) (by decide) (fun _ => by decide) (by decide)

end Production

#print axioms mcaEvent_dim1_of_line
#print axioms epsMCA_ge_candidate_pair
#print axioms epsMCA_ge_exactMass
#print axioms exact_repetition_epsMCA
#print axioms exact_repetition_epsMCA_concurrency
#print axioms production_first_prime
#print axioms production_second_prime
#print axioms exactMass_production_table

end ArkLib.ProximityGap.Frontier.ExactRepetitionMass
